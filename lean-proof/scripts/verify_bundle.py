#!/usr/bin/env python3
"""Verify the delivered source archive's file hashes using Python's stdlib."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'SOURCE_MANIFEST.json'


def verify(root=ROOT):
    root = Path(root)
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    records = manifest['files']
    assert manifest['format'] == 'qldpc-source-manifest-v1'
    for rel, record in records.items():
        path = root / rel
        assert not Path(rel).is_absolute() and '..' not in Path(rel).parts, rel
        data = path.read_bytes()
        assert len(data) == record['bytes'], f'Size mismatch: {rel}'
        assert hashlib.sha256(data).hexdigest() == record['sha256'], f'Hash mismatch: {rel}'
        if path.suffix == '.json':
            json.loads(data)
    checks = {}
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        digest, rel = line.split('  ', 1)
        assert not Path(rel).is_absolute() and '..' not in Path(rel).parts, rel
        assert rel not in checks, f'Duplicate checksum: {rel}'
        checks[rel] = digest
        assert hashlib.sha256((root / rel).read_bytes()).hexdigest() == digest, rel
    assert set(checks) == set(records) | {'SOURCE_MANIFEST.json'}
    print(f'Verified {len(records)} delivered files and SOURCE_MANIFEST.json.')
    return records


if __name__ == '__main__':
    verify()
