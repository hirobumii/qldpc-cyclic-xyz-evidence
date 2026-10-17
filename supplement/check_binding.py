"""Check submitted instances against preserved proof inputs and minimal supports."""
import hashlib
import json
from pathlib import Path
import sys


def rank(rows):
    basis = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = value
                break
            value ^= basis[pivot]
    return len(basis)


def packed(row, n):
    return sum(1 << q for q in row["X"]) | sum(1 << (n + q) for q in row["Z"])


def main(path):
    doc = json.loads(path.read_text())
    n = doc["n"]
    if n not in (56, 88):
        raise ValueError("Only the two submitted instances are in scope")
    ell = n // 8
    root = Path(__file__).resolve().parents[1]
    original_path = root / "lean-proof" / "data" / f"xyz-degree-five-cube-L{ell}.json"
    original = json.loads(original_path.read_text())
    for key in ("n", "k", "code_type", "checks", "distance"):
        assert doc[key] == original[key], key
    expected = []
    for axis, kind in (("X", 0), ("X", 1), ("Z", 2), ("Z", 3), ("Y", 4)):
        for i in range(ell):
            support = []
            for q in range(8):
                q1, q2, q3 = (q >> 2) & 1, (q >> 1) & 1, q & 1
                shift = (0, q1 + 2*q2 + 3*q3, q1, 2*q2 + 3*q3, 2*q2)[kind]
                support.append(q * ell + (i + shift) % ell)
            expected.append({"X": support if axis in ("X", "Y") else [],
                             "Z": support if axis in ("Z", "Y") else []})
    assert doc["checks"]["S"] == expected, "constructor mismatch"
    rows = [packed(row, n) for row in expected]
    dim = rank(rows)
    assert dim == n - doc["k"] == (32 if n == 56 else 52)
    dims = []
    full_mask = (1 << (2*n)) - 1
    for row in expected:
        support = set(row["X"]) | set(row["Z"])
        support_mask = sum((1 << q) | (1 << (n+q)) for q in support)
        outside_mask = full_mask ^ support_mask
        dims.append(dim - rank([r & outside_mask for r in rows]))
    assert all(d == 1 for d in dims)
    for q in range(n):
        axes = {(int(q in r["X"]), int(q in r["Z"])) for r in expected}
        assert {(1, 0), (0, 1), (1, 1)} <= axes
        assert sum(q in set(r["X"]) | set(r["Z"]) for r in expected) == 5
    assert all(len(set(r["X"]) | set(r["Z"])) == 8 for r in expected)
    print(json.dumps({"n": n, "k": doc["k"], "rank": dim,
                      "original_json_sha256": hashlib.sha256(original_path.read_bytes()).hexdigest(),
                      "submitted_checks_and_witness_match": True,
                      "constructor_matches": True,
                      "supported_stabilizer_dimensions": dims,
                      "all_three_axes_at_each_qubit": True,
                      "non_lc_css_by_minimal_support_argument": True}, indent=2))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
