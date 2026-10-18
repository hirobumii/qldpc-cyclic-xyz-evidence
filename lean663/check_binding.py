#!/usr/bin/env python3
"""External JSON-to-Lean literal audit; SHA256 itself is not formalized in Lean."""
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
source = ROOT / 'data' / 'candidate.json'
raw = source.read_bytes()
doc = json.loads(raw)
binding = json.loads((ROOT / 'data' / 'input-binding.json').read_text())
candidate = (ROOT / 'Qec663Proof' / 'Binding663' / 'Candidate.lean').read_text()
assert hashlib.sha256(raw).hexdigest() == binding['candidate_sha256']
assert doc['n'] == 663 and doc['code_type'] == 'CSS'
for side, name in [('X', 'hx'), ('Z', 'hz')]:
    match = re.search(r'^def ' + name + r' : List \(List Nat\) := (\[.*?^\])', candidate, re.M | re.S)
    assert match, name
    actual = ast.literal_eval(match.group(1))
    assert actual == doc['checks'][side], side
    assert len(actual) == 156
for side, name in [('X', 'xWitnessSupport'), ('Z', 'zWitnessSupport')]:
    match = re.search(r'^def ' + name + r' : List Nat := (\[[^\n]+\])', candidate, re.M)
    assert match and ast.literal_eval(match.group(1)) == doc['distance'][side]['witness']
canonical = {s: sorted(sorted(int(q) for q in row) for row in doc['checks'][s]) for s in ('X', 'Z')}
check_hash = hashlib.sha256(json.dumps(canonical, separators=(',', ':'), sort_keys=True).encode('ascii')).hexdigest()
assert check_hash == binding['canonical_checks_sha256']
print(json.dumps({'passed': True, 'n': 663, 'rows_X': 156, 'rows_Z': 156,
                  'candidate_sha256': hashlib.sha256(raw).hexdigest(),
                  'checks_sha256': check_hash, 'scope': 'external literal transcription audit'}))
