#!/usr/bin/env python3
"""Split finite commutation proofs into kernel-checked import-chained chunks."""
import json,pathlib
root=pathlib.Path(__file__).resolve().parents[1]
out=root/'QLDPC'/'Commutation'; out.mkdir(exist_ok=True)
core='''import QLDPC.Candidates

namespace QLDPC

def checkPairwiseCommute (S : List (Pauli n)) : Bool :=
  S.all (fun p => S.all (fun q => !(p.symplectic q)))

theorem checkPairwiseCommute_sound (S : List (Pauli n))
    (h : checkPairwiseCommute S = true) : PairwiseCommute S := by
  intro p hp q hq
  simp only [checkPairwiseCommute, List.all_eq_true, Bool.not_eq_true] at h
  have hh := h p hp q hq
  unfold Commutes
  cases hs : p.symplectic q <;> simp_all

end QLDPC
'''
(out/'Core.lean').write_text(core)
rowsall=[]; data={}
for l in [7,11]:
 d=json.loads((root/f'data/xyz-degree-five-cube-L{l}.json').read_text()); data[l]=d
 for i,row in enumerate(d['checks']['S']):rowsall.append((l,d['n'],i,row))
lit=lambda row,n:f'(⟨{sum(1<<i for i in row["X"])}, {sum(1<<i for i in row["Z"])}⟩ : Pauli {n})'
previous='QLDPC.Commutation.Core'
for chunk,start in enumerate(range(0,len(rowsall),5)):
 lines=[f'import {previous}','','set_option Elab.async false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace QLDPC.Candidates','']
 for l,n,i,row in rowsall[start:start+5]:
  lines += [f'theorem l{l}_commute_row{i} : l{l}.all (fun q => !({lit(row,n)}.symplectic q)) = true := by decide','']
 lines+=['end QLDPC.Candidates','']
 name=f'Chunk{chunk:02d}'; (out/f'{name}.lean').write_text('\n'.join(lines)); previous=f'QLDPC.Commutation.{name}'
lines=[f'import {previous}','','set_option Elab.async false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace QLDPC.Candidates','']
for l,d in data.items():
 rows=d['checks']['S']; n=d['n']; expr='true'; proof='True.intro'
 for row in rows[::-1]:expr=f'(l{l}.all (fun q => !({lit(row,n)}.symplectic q))) && ({expr})'
 for i in range(len(rows)-1,-1,-1):proof=f'And.intro l{l}_commute_row{i} ({proof})'
 lines += [f'theorem l{l}_pairwise_commute : PairwiseCommute l{l} := by',f'  apply checkPairwiseCommute_sound',f'  change ({expr}) = true','  simp only [Bool.and_eq_true]',f'  exact {proof}','',f'theorem l{l}_check_weight : ∀ p ∈ l{l}, p.weight = 8 := by',f'  have h : l{l}.all (fun p => p.weight == 8) = true := by decide','  simpa only [List.all_eq_true, beq_iff_eq] using h','']
lines += ['end QLDPC.Candidates','']
(root/'QLDPC/Commutation.lean').write_text('\n'.join(lines))
