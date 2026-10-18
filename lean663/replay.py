#!/usr/bin/env python3
"""Build source modules in dependency order, with one compiler process at a time."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--fresh', action='store_true', help='remove only this project .lake build directory')
args = parser.parse_args()
if args.fresh:
    shutil.rmtree(ROOT / '.lake', ignore_errors=True)
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S')
logs = ROOT / 'build-logs' / stamp
logs.mkdir(parents=True)
lake = shutil.which('lake')
assert lake, 'Add the pinned Lean 4.19.0 bin directory to PATH first.'
lean = str(Path(lake).resolve().parent / 'lean')
version = subprocess.check_output([lean, '--version'], text=True).strip()
assert 'version 4.19.0,' in version, version
env = dict(os.environ, LEAN_NUM_THREADS='2')
subprocess.run(['python3', str(ROOT / 'check_binding.py')], check=True, env=env,
               stdout=(logs / 'binding.json').open('w'))
order = []
seen = set()


def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = ROOT / Path(*module.split('.')).with_suffix('.lean')
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for dep in line.split()[1:]:
                if dep.startswith('Qec663Proof.'):
                    visit(dep)
    order.append(module)


visit('Qec663Proof.Distance663')
records = []
start = time.monotonic()
for i, module in enumerate(order):
    command = [lake, '--no-cache', 'build', '+' + module + ':olean']
    before = time.monotonic()
    with (logs / f'{i:02}-{module}.log').open('w') as out:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    record = {'module': module, 'command': command, 'exit_code': result.returncode,
              'wall_seconds': round(time.monotonic()-before, 3)}
    records.append(record)
    print(json.dumps(record), flush=True)
    if result.returncode:
        (logs / 'result.json').write_text(json.dumps({'passed': False, 'records': records}, indent=2)+'\n')
        raise SystemExit(result.returncode)
with (logs / 'lake-build.log').open('w') as out:
    result = subprocess.run([lake, '--no-cache', 'build'], cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
assert result.returncode == 0, (logs / 'lake-build.log')
audit = ROOT / 'Audit.lean'
with (logs / 'axioms.txt').open('w') as out:
    result = subprocess.run([lake, 'env', 'lean', str(audit)], cwd=ROOT, env=env,
                            stdout=out, stderr=subprocess.STDOUT)
assert result.returncode == 0, (logs / 'axioms.txt')
axioms = (logs / 'axioms.txt').read_text()
assert 'sorryAx' not in axioms
assert 'Lean.ofReduceBool' in axioms
expected_axioms = {'propext', 'Classical.choice', 'Lean.ofReduceBool', 'Quot.sound'}
actual_axioms = [set(a.split(', ')) for a in re.findall(r'depends on axioms: \[([^\]]*)\]', axioms)]
assert len(actual_axioms) == 4 and all(a == expected_axioms for a in actual_axioms), actual_axioms
manifest = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.rglob('*.lean')) if '.lake' not in p.parts}
summary = {'passed': True, 'fresh_requested': args.fresh, 'lean_version': version,
           'records': records, 'wall_seconds': round(time.monotonic()-start, 3),
           'source_sha256': manifest, 'axioms_log': str((logs/'axioms.txt').relative_to(ROOT)),
           'final_axioms': sorted(expected_axioms),
           'trust': 'standard Lean axioms plus native_decide compiler/runtime (Lean.ofReduceBool)'}
(logs / 'result.json').write_text(json.dumps(summary, indent=2)+'\n')
(ROOT / 'LAST_REPLAY.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps({'passed': True, 'wall_seconds': summary['wall_seconds'], 'logs': str(logs)}))
