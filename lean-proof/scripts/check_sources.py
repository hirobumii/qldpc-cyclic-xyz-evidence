#!/usr/bin/env python3
"""Fail on trust escapes in the project proof sources (not vendor dependencies)."""
import pathlib,re,sys
root=pathlib.Path(__file__).resolve().parents[1]
for path in sorted((root/'QLDPC').rglob('*.lean')):
    text=path.read_text()
    # Remove comments before looking for forbidden declarations or tactics.
    # The source tree deliberately has no nested comments.
    text=re.sub(r'/\-.*?\-/','',text,flags=re.S)
    text=re.sub(r'--[^\n]*','',text)
    bad=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|ofReduceBool|ofReduceNat)\b',text)
    if bad:
        print(f'{path.relative_to(root)}: forbidden proof token(s): {bad}', file=sys.stderr)
        sys.exit(1)
print('Project proof source check: no admitted proofs, custom axioms, or native trust escapes.')
