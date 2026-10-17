"""Source-only, serial Lean rebuild, optionally staged while proofs finish.
The final stage rechecks source hashes and invalidates changed dependencies.
No project .olean is ever copied into the isolated snapshot.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,time
P=argparse.ArgumentParser();P.add_argument('--stage',choices=['foundation','final'],default='final');P.add_argument('--theorem',action='append',default=[]);P.add_argument('--snapshot',default='fresh-build');args=P.parse_args()
root=pathlib.Path(__file__).resolve().parents[1];dst=root/'audit'/args.snapshot;marker=dst/'AUDIT_SNAPSHOT'
if dst.exists() and not marker.exists():raise SystemExit(f'Refusing unrelated existing directory: {dst}')
dst.mkdir(exist_ok=True);marker.write_text('Independent source-only audit snapshot. No project oleans are copied.\n')
olean=dst/'olean';olean.mkdir(exist_ok=True)
lean=root/'.toolchain'/'lean-4.19.0-linux'/'bin'/'lean'
env=os.environ.copy();env['LEAN_PATH']=str(olean);env.pop('LEAN_SRC_PATH',None)
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest_path=dst/'source-manifest.json';old_manifest=json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
result_path=dst/'result.json'
summary=json.loads(result_path.read_text()) if result_path.exists() else {'started_utc':now(),'toolchain':subprocess.check_output([str(lean),'--version'],text=True).strip(),'toolchain_binary_sha256':sha(lean),'project_oleans_reused':False,'steps':[],'compiled_source_sha256':{},'stages':[]}
if summary['toolchain_binary_sha256']!=sha(lean):raise SystemExit('Toolchain binary changed; use a new snapshot.')
files=list((root/'QLDPC').rglob('*.lean'))
if (root/'QLDPC.lean').exists():files.append(root/'QLDPC.lean')
files+=list((root/'data').glob('*.json'))
files += [root/'Audit.lean',root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',root/'audit'/'AuditSanity.lean']
manifest={str(p.relative_to(root)):sha(p) for p in sorted(files)}
changed={p for p in set(manifest)|set(old_manifest) if manifest.get(p)!=old_manifest.get(p)}
old_modules={p.removesuffix('.lean').replace('/','.') for p in old_manifest if p.endswith('.lean') and not p.startswith('audit/')}
module_names={p.removesuffix('.lean').replace('/','.') for p in manifest if p.endswith('.lean') and not p.startswith('audit/')}
changed_modules={p.removesuffix('.lean').replace('/','.') for p in changed if p.endswith('.lean') and not p.startswith('audit/')}
for p in files:
 rel=p.relative_to(root);q=dst/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
module_paths={m:dst/pathlib.Path(*m.split('.')).with_suffix('.lean') for m in module_names}
deps={m:re.findall(r'^import\s+(QLDPC(?:\.[A-Za-z0-9_]+)*)\s*$',p.read_text(),re.M) for m,p in module_paths.items()}
invalid=set(changed_modules)
while True:
 more={m for m,ds in deps.items() if any(d in invalid for d in ds)}-invalid
 if not more:break
 invalid|=more
invalidated_built=[]
for mod in sorted(invalid):
 out=olean/pathlib.Path(*mod.split('.')).with_suffix('.olean')
 if out.exists():
  stale=dst/'stale'/str(len(summary['stages']))/pathlib.Path(*mod.split('.')).with_suffix('.olean');stale.parent.mkdir(parents=True,exist_ok=True);out.rename(stale);invalidated_built.append(mod)
 summary['compiled_source_sha256'].pop(mod,None)
seen=set();active=set();order=[]
def visit(mod):
 if mod in seen:return
 if mod in active:raise ValueError(f'Cyclic project imports: {mod}')
 if mod not in module_paths:raise ValueError(f'Missing project module: {mod}')
 active.add(mod)
 for dep in deps[mod]:visit(dep)
 active.remove(mod);seen.add(mod);order.append(mod)
if args.stage=='foundation':
 for m in ['QLDPC.Binding','QLDPC.Geometry','QLDPC.Commutation','QLDPC.RankSemantic','QLDPC.ParametersCore']:visit(m)
else:
 visit('QLDPC')
 for m in sorted(module_paths):visit(m)
stage={'name':args.stage,'started_utc':now(),'changed_sources':sorted(changed),'invalidated_previously_built_modules':invalidated_built,'module_order':order}
summary['stages'].append(stage);summary['all_steps_passed']=False
log=open(dst/'build.log','a',buffering=1);log.write('\nSTAGE '+args.stage+' '+now()+'\n')
def save():result_path.write_text(json.dumps(summary,indent=2)+'\n')
save()
def run(cmd,name):
 print(f'CHECK {name}',flush=True);log.write('\nCOMMAND '+repr(cmd)+'\n');log.flush();start=time.monotonic()
 p=subprocess.run(cmd,cwd=dst,env=env,stdout=log,stderr=subprocess.STDOUT)
 summary['steps'].append({'name':name,'stage':args.stage,'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-start,3)})
 save()
 if p.returncode:raise SystemExit(f'Failed {name}; see {dst}/build.log')
for mod in order:
 source=module_paths[mod];out=olean/pathlib.Path(*mod.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists() and summary['compiled_source_sha256'].get(mod)==sha(source):
  print(f'REUSE OWN CHECKED {mod}',flush=True);continue
 run([str(lean),'-j1','-o',str(out),str(source.relative_to(dst))],mod)
 summary['compiled_source_sha256'][mod]=sha(source);save()
def inputs_unchanged():
 current=list((root/'QLDPC').rglob('*.lean'))+list((root/'data').glob('*.json'))
 if (root/'QLDPC.lean').exists():current.append(root/'QLDPC.lean')
 current += [root/'Audit.lean',root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',root/'audit'/'AuditSanity.lean']
 return {str(p.relative_to(root)) for p in current}==set(manifest) and all((root/p).exists() and sha(root/p)==h for p,h in manifest.items())
stage['completed_utc']=now()
summary['source_unchanged_at_stage_end']=inputs_unchanged()
if args.stage=='final':
 theorems=args.theorem or re.findall(r'^#print axioms\s+(\S+)\s*$',(root/'Audit.lean').read_text(),re.M)
 if not theorems:raise SystemExit('No final theorem inventory supplied.')
 summary['requested_theorems']=theorems
 inspector=dst/'AuditFinal.lean';inspector.write_text('import QLDPC\n\n'+'\n'.join('#check '+t+'\n#print axioms '+t for t in theorems)+'\n')
 run([str(lean),'-j1','AuditFinal.lean'],'final-theorem-axioms')
 run([str(lean),'-j1','audit/AuditSanity.lean'],'independent-semantic-regressions')
 summary['source_unchanged_at_stage_end']=inputs_unchanged()
 if not summary['source_unchanged_at_stage_end']:
  save();raise SystemExit('Sources changed during final audit; rerun --stage final to invalidate/rebuild changed dependencies.')
 summary['completed_utc']=now();summary['all_steps_passed']=True
save();print(json.dumps({k:v for k,v in summary.items() if k not in ('compiled_source_sha256','stages','steps')},indent=2),flush=True)
