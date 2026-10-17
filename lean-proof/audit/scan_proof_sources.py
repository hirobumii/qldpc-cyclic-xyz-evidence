"""Conservative source audit, supplementary to transitive #print axioms."""
import hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[1]
files=sorted((root/'QLDPC').rglob('*.lean'))
if (root/'QLDPC.lean').exists():files.append(root/'QLDPC.lean')
if (root/'Audit.lean').exists():files.append(root/'Audit.lean')
def strip_comments_strings(text):
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2;out.extend('  ')
   elif text.startswith('-/',i):depth-=1;i+=2;out.extend('  ')
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif string:
   if text[i]=='\\' and i+1<len(text):out.extend('  ');i+=2
   elif text[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif text.startswith('/-',i):depth=1;i+=2;out.extend('  ')
  elif text.startswith('--',i):
   j=text.find('\n',i)
   if j<0:j=len(text)
   out.extend(' '*(j-i));i=j
  elif text[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(text[i]);i+=1
 return ''.join(out)
patterns={
 'incomplete_or_added_axiom':r'\b(?:sorry|admit|axiom)\b',
 'native_evaluation':r'\b(?:native_decide|bv_decide)\b|Lean\.ofReduceBool|Lean\.trustCompiler|\bdecide\s+\+native\b',
 'kernel_or_runtime_override':r'skipKernelTC|\b(?:unsafe|extern|implemented_by|initialize|builtin_initialize|run_elab|run_tac|elab|macro)\b|#eval',
}
findings=[];imports=[];hashes={}
for p in files:
 text=p.read_text();clean=strip_comments_strings(text);rel=str(p.relative_to(root));hashes[rel]=hashlib.sha256(p.read_bytes()).hexdigest()
 for kind,pat in patterns.items():
  for m in re.finditer(pat,clean):findings.append({'file':rel,'line':clean[:m.start()].count('\n')+1,'kind':kind,'token':m.group()})
 for m in re.finditer(r'^import\s+(.+)$',clean,re.M):
  imports.extend({'file':rel,'module':v} for v in m.group(1).split())
unknown=[x for x in imports if x['module'] not in ('Std','Lean') and not x['module'].startswith('QLDPC.') and x['module']!='QLDPC']
report={'files_scanned':len(files),'findings':findings,'unexpected_external_imports':unknown,'source_sha256':hashes,'limitations':'Static source scanning is supplementary; successful kernel compilation and final transitive axiom inspection are required. Official core/Std remains trusted.'}
(root/'audit'/'source_scan.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='source_sha256'},indent=2))
if findings or unknown:raise SystemExit(1)
