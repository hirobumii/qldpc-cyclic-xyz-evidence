"""Read simple Lean literal declarations independently of their generator.
The JSON and SHA256 relation is external audit evidence, not a Lean theorem.
"""
import ast,hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[1]
p=root/'QLDPC'/'Candidates.lean';text=p.read_text();results=[]
for L in (7,11):
 f=root/'data'/f'xyz-degree-five-cube-L{L}.json';d=json.loads(f.read_bytes());n=d['n']
 actual=ast.literal_eval(re.search(rf'def supports{L} : List \(List Nat × List Nat\) := (\[.*?\n\])',text,re.S).group(1))
 expected=[(r['X'],r['Z']) for r in d['checks']['S']]
 assert actual==expected
 m=re.search(rf'def l{L} : List \(Pauli {n}\) := (\[.*?\n\])',text,re.S)
 packed=ast.literal_eval(m.group(1).replace('⟨','(').replace('⟩',')'))
 masks=lambda ns:sum(1<<i for i in ns)
 assert packed==[(masks(x),masks(z)) for x,z in expected]
 assert all(0<=a<1<<n and 0<=b<1<<n for a,b in packed)
 w=re.search(rf'def witness{L} : Pauli {n} := ⟨(\d+), (\d+)⟩',text)
 assert tuple(map(int,w.groups()))==(masks(d['distance']['P']['witness']['X']),masks(d['distance']['P']['witness']['Z']))
 results.append({'L':L,'support_lists_exactly_match_json':True,'packed_rows_exactly_match_json':True,'witness_exactly_matches_json':True,'no_integer_truncation':True,'json_sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
out={'candidate_lean_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'results':results,'formalized_boundary':'Lean proves the literals in Candidates.lean are equal under ofSupports; parsing JSON, comparing copied files, and SHA256 are external audit operations.'}
(root/'audit'/'literal_binding.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
