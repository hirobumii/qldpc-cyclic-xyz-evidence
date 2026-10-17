"""Independent, nonformal audit. This is evidence, not a Lean proof."""
import argparse,hashlib,json,pathlib,itertools
ROOT=pathlib.Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--original-dir',type=pathlib.Path,help='Optional original research candidate directory for byte-for-byte source comparison.')
args=parser.parse_args()
ORIG=args.original_dir

def mask(a): return sum(1<<i for i in a)
def sp(a,b,n):
    m=(1<<n)-1
    return ((((a&m)&(b>>n))^((a>>n)&(b&m))).bit_count()&1)
def echelon(rows):
    piv={}; deps=[]
    for i,v in enumerate(rows):
        c=1<<i
        while v:
            k=v.bit_length()-1
            if k not in piv: piv[k]=(v,c); break
            w,d=piv[k]; v^=w;c^=d
        else: deps.append(c)
    return piv,deps

def residual(piv,v):
    for k,(w,_) in sorted(piv.items(),reverse=True):
        if (v>>k)&1:v^=w
    return v

def mul(a,b):
    # i^phase X^x Z^z, tensor convention. Y = iXZ.
    x,z,phase=a;u,v,psi=b
    return x^u,z^v,(phase+psi+2*(z&u).bit_count())%4

def positive_pauli(v,n):
    m=(1<<n)-1;x=v&m;z=v>>n
    return x,z,(x&z).bit_count()%4

def product(rows,subset,n):
    out=(0,0,0)
    for i,v in enumerate(rows):
        if subset>>i&1: out=mul(out,positive_pauli(v,n))
    return out

results=[]
for L in (7,11):
    fn=f'xyz-degree-five-cube-L{L}.json';f=ROOT/'data'/fn
    d=json.loads(f.read_bytes());n=d['n'];checks=d['checks']['S']
    original_matches_copy=None
    if ORIG is not None:
        assert f.read_bytes()==(ORIG/fn).read_bytes()
        original_matches_copy=True
    assert all(len(v[k])==len(set(v[k])) and all(0<=i<n for i in v[k]) for v in checks for k in ('X','Z'))
    rows=[mask(v['X']) | (mask(v['Z'])<<n) for v in checks]
    expected=[]
    for axis,v in [('X',(0,0,0)),('X',(1,1,1)),('Z',(1,0,0)),('Z',(0,1,1)),('Y',(0,1,0))]:
        for sheet in range(L):
            bits=[q*L+(sheet+v[0]*((q>>2)&1)+2*v[1]*((q>>1)&1)+3*v[2]*(q&1))%L for q in range(8)]
            b=mask(bits);expected.append(b if axis=='X' else b<<n if axis=='Z' else b|(b<<n))
    assert rows==expected
    piv,deps=echelon(rows)
    assert len(piv)==5*L-3 and len(deps)==3
    assert all(sp(a,b,n)==0 for a in rows for b in rows)
    signed_relations=[{'indices':[i for i in range(len(rows)) if c>>i&1], 'product_i_phase_X_Z':product(rows,c,n)} for c in deps]
    assert all(tuple(t['product_i_phase_X_Z'])==(0,0,0) for t in signed_relations)
    # All 2^3 dependency combinations are checked separately, too.
    for subset in range(1<<len(deps)):
        c=0
        for i,x in enumerate(deps):
            if subset>>i&1:c^=x
        assert product(rows,c,n)==(0,0,0)
    errors=[];by_syndrome={}
    for q in range(n):
        for axis,v in [('X',1<<q),('Z',1<<(q+n)),('Y',(1<<q)|(1<<(q+n)))]:
            syn=sum(sp(v,r,n)<<i for i,r in enumerate(rows))
            assert syn!=0
            errors.append((q,axis,v,syn));by_syndrome.setdefault(syn,[]).append((q,axis))
    assert len(by_syndrome)==3*n
    pair_checks=0
    for a,b in itertools.combinations(errors,2):
        if a[0]==b[0]:continue
        pair_checks+=1
        assert a[3]!=b[3]
        assert all(q in (a[0],b[0]) for q,ax in by_syndrome.get(a[3]^b[3],[]))
    w=d['distance']['P']['witness'];w=mask(w['X'])|(mask(w['Z'])<<n)
    assert all(sp(w,r,n)==0 for r in rows) and residual(piv,w)!=0
    m=(1<<n)-1
    assert ((w&m)|(w>>n)).bit_count()==4
    weights=[((r&m)|(r>>n)).bit_count() for r in rows]
    degree=[sum(bool(((r&m)|(r>>n))>>q&1) for r in rows) for q in range(n)]
    assert set(weights)=={8} and set(degree)=={5}
    result={'L':L,'n':n,'semantic_binary_rank_externally_checked':len(piv),'k':n-len(piv),'candidate_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'original_matches_copy':original_matches_copy,'rows_equal_report_constructor':True,'pairwise_commute':True,'check_weight':8,'qubit_degree':5,'single_errors':len(errors),'distinct_site_pairs_audited':pair_checks,'no_weight_1_2_3_normalizer':True,'weight_four_logical_checked':True,'plus_sign_dependency_basis':signed_relations,'all_eight_dependencies_multiply_to_positive_identity':True,'formal_proof':False}
    results.append(result)
# A small commuting unsigned generator set need not yield a nonempty all-plus code.
bad=[(3,0,0),(0,3,0),(3,3,2)] # XX, ZZ, YY
out=(0,0,0)
for p in bad:out=mul(out,p)
assert out==(0,0,2)
report={'original_source_comparison_repeated':ORIG is not None,'original_source_comparison_note':'Original source files compared byte for byte.' if ORIG is not None else 'Original research source comparison was not repeated. Only bundled candidate data were audited; use --original-dir to compare against originals.','results':results,'phase_bridge_counterexample':{'generators':['XX','ZZ','YY'],'pairwise_commute':True,'unsigned_rank':2,'product':'-I','all_plus_codespace_dimension':0},'limitations':['These Python checks are independent external evidence, not kernel checked theorems.','The JSON has no generator signs. All-plus Hermitian representatives are an explicitly chosen interpretation.','No Hilbert-space formalization follows from these runtime checks.']}
(ROOT/'audit'/'independent_candidate_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
