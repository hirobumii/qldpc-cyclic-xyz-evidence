#!/usr/bin/env python3
"""Make a deterministic, source-only delivery after final audit and human coordination.

This script deliberately refuses a package without the final audit artifacts.
It does not compile Lean, download software, or publish/upload anything.
"""
from pathlib import Path
import argparse
import hashlib
import json
import stat
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
NAME = 'qldpc-lean-finite-20261017'
ROOT_FILES = [
    '.gitignore', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'env.sh',
    'README.md', 'README.zh-CN.md', 'TOOLCHAIN.md', 'RANK_WITNESS_NOTES.md',
    'Audit.lean', 'AuditFoundation.lean', 'QLDPC.lean', 'generate_rank_certificates.py',
]
AUDIT_FILES = [
    'REVIEW.md', 'independent_candidate_audit.py', 'independent_candidate_audit.json',
    'check_literal_binding.py', 'literal_binding.json', 'AuditSanity.lean',
    'sanity-build.log', 'run_fresh_audit.py', 'final-build.log', 'final-result.json',
    'source-manifest.json', 'scan_proof_sources.py', 'source_scan.json', 'finalize_audit.py',
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_files():
    files = [ROOT / name for name in ROOT_FILES]
    files += [ROOT / 'audit' / name for name in AUDIT_FILES]
    for directory, patterns in [
        ('QLDPC', ['*.lean']), ('data', ['*.json']),
        ('scripts', ['*.py', '*.sh']), ('tools', ['*.py']),
        ('logs', ['*.txt', '*.log', '*.json']),
    ]:
        for pattern in patterns:
            files += list((ROOT / directory).rglob(pattern) if directory == 'QLDPC' else (ROOT / directory).glob(pattern))
    unique = sorted(set(files))
    for path in unique:
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f'Missing or non-regular final file: {path.relative_to(ROOT)}')
    return unique


def validate_final_audit(files):
    result = json.loads((ROOT / 'audit/final-result.json').read_text())
    if result.get('all_steps_passed') is not True:
        raise SystemExit('Final audit did not pass all steps.')
    if result.get('source_unchanged_at_stage_end', result.get('source_unchanged_during_audit')) is not True:
        raise SystemExit('Final audited sources were not verified unchanged.')
    if result.get('project_oleans_reused') is not False:
        raise SystemExit('Final audit reused project oleans or did not report this property.')
    if not result.get('completed_utc'):
        raise SystemExit('Final audit lacks completion time.')
    if not result.get('steps') or any(step.get('exit_code') != 0 for step in result['steps']):
        raise SystemExit('Final audit has a failed or missing build step.')
    for theorem in ['QLDPC.xyz56_parameters', 'QLDPC.xyz88_parameters']:
        if theorem not in result.get('requested_theorems', []):
            raise SystemExit(f'Missing final theorem audit: {theorem}')
    if result.get('final_live_source_hashes_match_snapshot') is not True:
        raise SystemExit('Final report has not confirmed live-source identity.')
    axiom_audit = result.get('axiom_audit', {})
    if axiom_audit.get('all_printed_theorems_use_only_standard_axioms') is not True:
        raise SystemExit('Final transitive axiom audit is incomplete.')
    standard = {'propext', 'Classical.choice', 'Quot.sound'}
    for theorem in ['QLDPC.xyz56_parameters', 'QLDPC.xyz88_parameters']:
        if set(axiom_audit.get('final_theorem_axioms', {}).get(theorem, [])) != standard:
            raise SystemExit(f'Unexpected final main-theorem axioms: {theorem}')
    audited = json.loads((ROOT / 'audit/source-manifest.json').read_text())
    for rel, digest in audited.items():
        if sha((ROOT / rel).read_bytes()) != digest:
            raise SystemExit(f'Source changed since the final audit: {rel}')
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if (rel.startswith('QLDPC/') and path.suffix == '.lean') or rel == 'QLDPC.lean':
            if rel not in audited:
                raise SystemExit(f'Lean module absent from final audit manifest: {rel}')
    scan = json.loads((ROOT / 'audit/source_scan.json').read_text())
    if scan.get('findings') or scan.get('unexpected_external_imports'):
        raise SystemExit('Final static proof-source scan has findings.')
    for rel, digest in scan.get('source_sha256', {}).items():
        if sha((ROOT / rel).read_bytes()) != digest:
            raise SystemExit(f'Source changed since static scan: {rel}')
    proof_paths = {str(p.relative_to(ROOT)) for p in files
                   if (str(p.relative_to(ROOT)).startswith('QLDPC/') and p.suffix == '.lean')
                   or p in (ROOT / 'QLDPC.lean', ROOT / 'Audit.lean')}
    if proof_paths != set(scan.get('source_sha256', {})):
        raise SystemExit('Final static scan does not cover exactly the packaged proof modules.')
    binding = json.loads((ROOT / 'audit/literal_binding.json').read_text())
    if binding.get('candidate_lean_sha256') != sha((ROOT/'QLDPC/Candidates.lean').read_bytes()):
        raise SystemExit('Literal binding report is stale.')
    for entry in binding.get('results', []):
        candidate = ROOT/'data'/f'xyz-degree-five-cube-L{entry["L"]}.json'
        if entry.get('json_sha256') != sha(candidate.read_bytes()):
            raise SystemExit('Candidate JSON changed since literal binding report.')
    review = (ROOT / 'audit/REVIEW.md').read_text().lower()
    if 'status: **in progress**' in review:
        raise SystemExit('Independent review still says in progress.')
    if '等待最终独立干净构建' in (ROOT / 'README.zh-CN.md').read_text():
        raise SystemExit('Chinese README still has its draft status.')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--confirmed-final', action='store_true',
                   help='Use only after parent and auditor both confirm final-source readiness.')
    args = p.parse_args()
    if not args.confirmed_final:
        raise SystemExit('Refusing to freeze without --confirmed-final and final audit checks.')
    files = source_files()
    result = validate_final_audit(files)
    payload = {}
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        data = path.read_bytes()
        if path.suffix == '.json':
            json.loads(data)
        payload[rel] = (data, 0o755 if path.suffix == '.sh' else 0o644)
    manifest = {
        'format': 'qldpc-source-manifest-v1',
        'scope': 'Two finite phase-free binary-symplectic candidates; external JSON and physical-interpretation boundaries apply.',
        'files': {rel: {'sha256': sha(data), 'bytes': len(data)} for rel, (data, _) in sorted(payload.items())},
    }
    payload['SOURCE_MANIFEST.json'] = ((json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode(), 0o644)
    checksum_text = ''.join(f'{sha(data)}  {rel}\n' for rel, (data, _) in sorted(payload.items()))
    payload['SHA256SUMS'] = (checksum_text.encode(), 0o644)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    archive = args.output_dir / (NAME + '.zip')
    if archive.exists():
        raise SystemExit(f'Refusing to overwrite existing final archive: {archive}')
    temp_archive = archive.with_suffix('.zip.tmp')
    with zipfile.ZipFile(temp_archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for rel, (data, mode) in sorted(payload.items()):
            info = zipfile.ZipInfo(f'{NAME}/{rel}', date_time=(2026, 10, 17, 0, 0, 0))
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | mode) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, data, compresslevel=9)
    if temp_archive.stat().st_size >= 50_000_000:
        raise SystemExit('Source archive unexpectedly exceeds the 50 MB delivery limit.')
    with zipfile.ZipFile(temp_archive) as z:
        if z.testzip() is not None:
            raise SystemExit('ZIP CRC check failed.')
        expected = {f'{NAME}/{rel}' for rel in payload}
        if set(z.namelist()) != expected or len(z.namelist()) != len(expected):
            raise SystemExit('Archive membership mismatch or duplicate entries.')
        for rel, (data, _) in payload.items():
            actual = z.read(f'{NAME}/{rel}')
            if sha(actual) != sha(data):
                raise SystemExit(f'Archive hash mismatch: {rel}')
            if rel.endswith('.json'):
                json.loads(actual)
        with tempfile.TemporaryDirectory(prefix='qldpc-package-check-') as tmp:
            z.extractall(tmp)
            import importlib.util
            spec = importlib.util.spec_from_file_location('bundle_verifier', Path(tmp)/NAME/'scripts/verify_bundle.py')
            verifier = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(verifier)
            verifier.verify(Path(tmp)/NAME)
    # Refuse a package if any selected input changed while it was being read.
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if path.read_bytes() != payload[rel][0]:
            raise SystemExit(f'Packaging input changed during snapshot: {rel}')
    temp_archive.rename(archive)
    digest = sha(archive.read_bytes())
    (args.output_dir/(archive.name+'.sha256')).write_text(f'{digest}  {archive.name}\n')
    report = {
        'archive': archive.name, 'sha256': digest, 'bytes': archive.stat().st_size,
        'archived_files': len(payload), 'json_files_parsed': sum(rel.endswith('.json') for rel in payload),
        'zip_crc_passed': True, 'all_file_hashes_passed': True,
        'source_unchanged_during_packaging': True,
        'final_audit_completed_utc': result['completed_utc'],
        'excluded': ['toolchain', 'project build artifacts', 'temporary audit snapshots', 'private notes'],
    }
    (args.output_dir/'PACKAGE_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
