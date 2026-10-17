#!/usr/bin/env python3
"""Transcribe immutable input JSON into Lean literals; not a correctness oracle.
Every transcription is checked by Lean's candidate_binding theorems.
"""
import json, pathlib, hashlib
root=pathlib.Path(__file__).resolve().parents[1]
lines=['import QLDPC.Basic', '', 'namespace QLDPC.Candidates', '']
manifest={}
for l in (7,11):
    path=root/'data'/f'xyz-degree-five-cube-L{l}.json'
    data=json.loads(path.read_text()); n=data['n']
    manifest[path.name]={'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'n':n,'k_metadata':data['k']}
    rows=data['checks']['S']
    fmt=lambda ns:'['+', '.join(map(str,ns))+']'
    mask=lambda ns:sum(1<<i for i in ns)
    lines += [f'/-- Original JSON X/Z support lists, in original row order. -/',f'def supports{l} : List (List Nat × List Nat) := [']
    lines += ['  ('+fmt(row['X'])+', '+fmt(row['Z'])+')'+(',' if i+1<len(rows) else '') for i,row in enumerate(rows)]
    lines += [']','', f'/-- Bit-packed transcription of the {n}-qubit input candidate. -/',f'def l{l} : List (Pauli {n}) := [']
    lines += [f'  ⟨{mask(row["X"])}, {mask(row["Z"])}⟩'+(',' if i+1<len(rows) else '') for i,row in enumerate(rows)]
    lines += [']','']
    w=data['distance']['P']['witness']
    lines += [f'def witness{l} : Pauli {n} := ⟨{mask(w["X"])}, {mask(w["Z"])}⟩', '', f'theorem l{l}_candidate_binding :',f'    l{l} = supports{l}.map (fun s => Pauli.ofSupports s.1 s.2) := by decide','',f'theorem l{l}_row_count : l{l}.length = {len(rows)} := by decide','',f'theorem witness{l}_weight : witness{l}.weight = 4 := by decide','']
lines += ['end QLDPC.Candidates','']
(root/'QLDPC'/'Candidates.lean').write_text('\n'.join(lines))
(root/'data'/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
