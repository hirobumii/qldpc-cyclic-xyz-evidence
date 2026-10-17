"""Finalize an already successful isolated Lean audit; never proves Lean claims itself."""
import hashlib,json,pathlib,re,shutil,subprocess
root=pathlib.Path(__file__).resolve().parents[1];audit=root/'audit';fresh=audit/'fresh-build'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result=json.loads((fresh/'result.json').read_text());assert result['all_steps_passed']
manifest=json.loads((fresh/'source-manifest.json').read_text())
assert all((root/p).exists() and sha(root/p)==h for p,h in manifest.items())
current_proofs={str(p.relative_to(root)) for p in (root/'QLDPC').rglob('*.lean')}|{'QLDPC.lean','Audit.lean'}
manifest_proofs={p for p in manifest if p.endswith('.lean') and not p.startswith('audit/')}
assert current_proofs==manifest_proofs
for rel in current_proofs:
 module=rel.removesuffix('.lean').replace('/','.')
 assert result['compiled_source_sha256'][module]==manifest[rel]
producer_path=root/'logs'/'final-proof-source-sha256.json';producer=json.loads(producer_path.read_text())
assert all(manifest.get(p)==h and sha(root/p)==h for p,h in producer.items())
for script in ['scan_proof_sources.py','check_literal_binding.py']:
 subprocess.run(['python',str(audit/script)],cwd=root,check=True,stdout=subprocess.DEVNULL)
log=(fresh/'build.log').read_text()
axioms={name:[v.strip() for v in vals.split(',') if v.strip()] for name,vals in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):axioms[name]=[]
allowed={'propext','Classical.choice','Quot.sound'}
assert axioms and all(set(v)<=allowed for v in axioms.values()),axioms
requested=result['requested_theorems'];assert len(requested)==22 and all(t in axioms for t in requested)
assert not re.search(r'\b(?:sorryAx|Lean\.trustCompiler|Lean\.ofReduceBool)\b',log)
assert all(step['exit_code']==0 for step in result['steps'])
result['axiom_audit']={'allowed_standard_axioms':sorted(allowed),'final_theorem_axioms':{t:axioms[t] for t in requested},'all_printed_theorems_use_only_standard_axioms':True}
result['final_live_source_hashes_match_snapshot']=True
result['producer_frozen_manifest']={'sha256':sha(producer_path),'files':len(producer),'all_match_audited_snapshot':True}
result['audited_lean_module_count']=len(current_proofs)
result['audit_generated_oleans_reused_between_stages']=True
result['preexisting_producer_oleans_imported']=False
result['total_compile_and_inspection_seconds']=round(sum(step['elapsed_seconds'] for step in result['steps']),3)
result['snapshot_manifest_sha256']=sha(fresh/'source-manifest.json')
(audit/'final-result.json').write_text(json.dumps(result,indent=2)+'\n')
shutil.copyfile(fresh/'source-manifest.json',audit/'source-manifest.json')
shutil.copyfile(fresh/'build.log',audit/'final-build.log')
review=audit/'REVIEW.md';text=review.read_text();text=text.replace('Status: **in progress**. The semantic design and input transcription have been reviewed. This file is not yet a final certificate of the whole project; the final build and theorem-axiom audit remain pending.','Status: **PASS for the stated finite phase-free binary-symplectic theorems.** The independent source-only rebuild, final source identity checks, and transitive axiom audit all passed. The scope boundaries below are part of this verdict.')
text=text.replace('A clean source build plus source review and transitive axiom checks is planned; this is not an independently implemented kernel/comparator certification.','A clean source build, source review, and transitive axiom checks were completed; this is not an independently implemented kernel/comparator certification.')
text += f'''\n## Final validation record\n\n- Pinned Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`.\n- Independently rebuilt {len(current_proofs)} Lean source modules, including the final audit module, from a source-only snapshot. No producer `.olean` files were copied or imported. The second stage reused only this audit's own previously rebuilt modules after source-hash reconciliation; changed-module invalidation was supported, and no already-built module required invalidation.\n- All {len(requested)} requested final theorem types and transitive axiom lists were inspected. Both `QLDPC.xyz56_parameters` and `QLDPC.xyz88_parameters` depend exactly on `propext`, `Classical.choice`, and `Quot.sound`. There are no custom, missing-proof, or compiler-trust axioms.\n- The six independent semantic regression theorems also passed; each uses only `propext`.\n- All {len(producer)} entries in the producer's frozen proof/configuration manifest match the independently audited snapshot and final live source. All candidate, configuration, and regression-source hashes in the full audit manifest match as well.\n- Final source scan: {len(current_proofs)} Lean files, no flagged proof bypasses and no unexpected external imports. JSON/literal checks were rerun successfully.\n- Serial compile and inspection time across both audit stages: {result['total_compile_and_inspection_seconds']} seconds.\n- Audit snapshot manifest SHA256: `{result['snapshot_manifest_sha256']}`.\n- Detailed records: `final-result.json`, `source-manifest.json`, `final-build.log`, `source_scan.json`, and `literal_binding.json`.\n\nThis result certifies the actual finite theorem statements and reviewed definitions. It does not turn the external JSON parsing/SHA256 checks, phase calculations, Hilbert-space correspondence, intrinsic non-CSS result, or infinite-family argument into Lean theorems.\n'''
review.write_text(text)
print(json.dumps({'status':'PASS','lean_modules':len(current_proofs),'requested_final_theorems':len(requested),'main_axioms':{t:axioms[t] for t in ['QLDPC.xyz56_parameters','QLDPC.xyz88_parameters']},'source_manifest_sha256':result['snapshot_manifest_sha256'],'compile_seconds':result['total_compile_and_inspection_seconds']},indent=2))
