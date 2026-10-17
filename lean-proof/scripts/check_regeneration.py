#!/usr/bin/env python3
"""Regenerate certificates in a temporary copy, never in the working proof tree."""
from pathlib import Path
import hashlib
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
GENERATORS = [
    'scripts/generate_candidates.py',
    'scripts/generate_commutation.py',
    'generate_rank_certificates.py',
    'tools/generate_distance.py',
]


def main():
    initial = {str(p.relative_to(ROOT)): p.read_bytes() for p in (ROOT/'QLDPC').rglob('*.lean')}
    initial['data/manifest.json'] = (ROOT/'data/manifest.json').read_bytes()
    with tempfile.TemporaryDirectory(prefix='qldpc-regeneration-') as temp:
        dst = Path(temp)
        shutil.copytree(ROOT/'QLDPC', dst/'QLDPC')
        shutil.copytree(ROOT/'data', dst/'data')
        for generator in GENERATORS:
            target = dst/generator
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT/generator, target)
            result = subprocess.run([sys.executable, str(target)], cwd=dst,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(f'COMMAND python3 {generator}\n{result.stdout}', end='')
            if result.returncode:
                raise SystemExit(f'Generator failed ({result.returncode}): {generator}')
        actual = {str(p.relative_to(dst)): p.read_bytes() for p in (dst/'QLDPC').rglob('*.lean')}
        actual['data/manifest.json'] = (dst/'data/manifest.json').read_bytes()
        changed = sorted(k for k in initial.keys() | actual.keys() if initial.get(k) != actual.get(k))
        if changed:
            raise SystemExit('Regeneration changed delivered source: ' + ', '.join(changed))
    for rel, original in initial.items():
        if (ROOT/rel).read_bytes() != original:
            raise SystemExit('Working source changed during check: ' + rel)
    print(f'PASS: all {len(GENERATORS)} generators reproduce byte-for-byte; {len(initial)} source/data files checked.')
    for generator in GENERATORS:
        print(hashlib.sha256((ROOT/generator).read_bytes()).hexdigest()+'  '+generator)


if __name__ == '__main__':
    main()
