#!/usr/bin/env python3
"""Fresh source-only build, literal regeneration, and exact axiom audit."""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--toolchain-bin', type=Path, required=True)
p.add_argument('--out', type=Path)
args = p.parse_args()
out = args.out or Path(tempfile.mkdtemp(prefix='qldpc1000-lean-replay-'))
out.mkdir(parents=True, exist_ok=True)
project = out / 'project'
project.mkdir()
files = [ROOT/'Qldpc1000.lean',ROOT/'lakefile.toml',ROOT/'lean-toolchain',
         ROOT/'generate_data.py',ROOT/'source.json',ROOT/'SearchDependencyAudit.lean'] + sorted((ROOT/'Qldpc1000').glob('*.lean'))
hashes = {}
for f in files:
    relative = f.relative_to(ROOT)
    dest = project/relative
    dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(f,dest)
    hashes[str(relative)] = hashlib.sha256(f.read_bytes()).hexdigest()
    if f.suffix == '.lean':
        assert not re.search(r'\b(sorry|admit|unsafe|extern|native_decide)\b|^\s*axiom\b',f.read_text(),re.M), f
before = (project/'Qldpc1000/Data.lean').read_bytes()
subprocess.run(['python3','generate_data.py'],cwd=project,check=True,capture_output=True)
assert before == (project/'Qldpc1000/Data.lean').read_bytes(), 'Literal generation drift'
lean,lake = args.toolchain_bin/'lean',args.toolchain_bin/'lake'
version = subprocess.check_output([str(lean),'--version'],text=True).strip()
assert '4.35.0' in version,version
run = subprocess.run([str(lake),'--no-cache','build'],cwd=project,text=True,capture_output=True)
log = run.stdout+run.stderr
(out/'build.log').write_text(log)
print(log)
assert run.returncode == 0, 'Fresh build failed; inspect build.log'
assert 'sorryAx' not in log
axioms = {}
for theorem,body in re.findall(r"'(Qldpc1000\.[^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):
    names = [x.strip() for x in body.split(',') if x.strip()]
    axioms[theorem] = names
base = {'propext','Classical.choice','Quot.sound'}
constructive = {'propext','Quot.sound'}
expected = {
    'bulk_transpose':{'propext'},
    'recipe_values':constructive,
    'local_cover':base,
    'LocalFormula.column_formula':base,
    'LocalFormula.neighbors_perm':base,
    'two_atoms':base,
    'four_atoms':base,
    'four_edges_impossible':base,
    'small_bipartite_impossible':base,
    'shore_syndromes_zero':base,
    'Cayley.difference_distinct':constructive,
    'Cayley.difference_injective':constructive,
    'Cayley.common_neighbors':constructive,
    'Cayley.signed_flips':base,
    'AlgebraicLocal.edge_simple':base,
    'AlgebraicLocal.no_rectangle':base,
    'AlgebraicLocal.formula_endpoints':constructive,
    'AlgebraicLocal.no_small':base,
    'AlgebraicLocal.shore_boundary_injective':constructive,
    'AlgebraicLocal.formula_nonedge':base,
    'designated_phase_separation':constructive,
    'nonedge_checked':base,
    'structural_lower':base,
    'syndrome_zero_of_vector_map_zero':base,
    'full_stored_kernel':constructive,
    'css_commutes':base,
    'Commutation.mul_assoc':constructive,
    'Commutation.product_rows_commute':base,
    'Commutation.stored_formula':base,
    'literal_kernel_minimum':base,
    'x_logical':base,
    'z_logical':base,
    'pauli_lower':base,
    'dX_eq_six':base,
    'dZ_eq_six':base,
    'd_eq_six':base,
    'exact_distance':base,
    'certified_public_code':base}
expected = {'Qldpc1000.'+name:value for name,value in expected.items()}
assert set(axioms)==set(expected), ('Unexpected or missing theorem audits',set(axioms)^set(expected))
for name,values in expected.items():
    assert set(axioms[name])==values,(name,'Unexpected/missing axioms',set(axioms[name])^values)
strict = subprocess.run([str(lake),'env','lean','--trust=0','Qldpc1000/Audit.lean'],
                        cwd=project,text=True,capture_output=True)
strict_log = strict.stdout+strict.stderr
(out/'kernel-trust-zero.log').write_text(strict_log)
assert strict.returncode == 0, 'Kernel trust=0 audit failed'
strict_axioms = {}
for theorem,body in re.findall(r"'(Qldpc1000\.[^']+)' depends on axioms:\s*\[([^\]]*)\]",strict_log,re.S):
    strict_axioms[theorem] = {x.strip() for x in body.split(',') if x.strip()}
assert strict_axioms == expected, 'Kernel trust=0 exact allowlist mismatch'
closure = subprocess.run([str(lake),'env','lean','--trust=0','SearchDependencyAudit.lean'],
                         cwd=project,text=True,capture_output=True)
closure_log = closure.stdout+closure.stderr
(out/'search-dependencies.log').write_text(closure_log)
assert closure.returncode == 0, 'Dependency closure audit failed'
closures = re.findall(r'ROOT (Qldpc1000\.[^:]+): (\d+) project dependencies; SEARCH \[([^\]]*)\]',closure_log)
assert {name for name,_,_ in closures} == {'Qldpc1000.exact_distance','Qldpc1000.certified_public_code'}
assert len(closures) == 2 and all(not names.strip() for _,_,names in closures), closures
source = (project/'source.json').read_bytes()
audit = {'status':'PASS','lean_version':version,'source_bytes':len(source),
         'source_sha256':hashlib.sha256(source).hexdigest(),
         'source_git_blob':hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest(),
         'source_regeneration_identical':True,'source_only_fresh_build':True,
         'lake_no_cache':True,
         'exact_per_theorem_axiom_allowlists_pass':True,
         'no_sorry_admit_custom_axiom_unsafe_extern':True,
         'no_native_evaluation_axioms':True,'native_axiom_count':0,
         'kernel_trust_zero_pass':True,
         'no_old_search_or_pair_enumeration_dependencies':True,
         'dependency_closures':{name:int(count) for name,count,_ in closures},
         'rank_dimension_formalized':False,
         'css_commutation_kernel_only':True,
         'trust_boundary':'Lean kernel and listed standard axioms; external JSON identity is an artifact-binding check',
         'axioms':axioms,'source_files_sha256':hashes}
(out/'audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
print('PASS:',out/'audit.json')
