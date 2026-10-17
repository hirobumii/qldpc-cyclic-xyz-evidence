#!/usr/bin/env python3
"""Generate exact syndrome certificate data; Lean, not this script, checks it."""
import json,pathlib
root=pathlib.Path(__file__).resolve().parents[1]
src=root/'data'
out=['import QLDPC.Candidates','import QLDPC.DistanceCore','','set_option Elab.async false','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','','namespace QLDPC.DistanceProof','open QLDPC.Candidates','']
def tree(vals):
 if not vals:return '.empty'
 k=len(vals)//2
 return f'(.node {vals[k]} {tree(vals[:k])} {tree(vals[k+1:])})'
for L in [7,11]:
 d=json.load(open(src/f'xyz-degree-five-cube-L{L}.json'));n=d['n']; rows=d['checks']['S'];m=len(rows)
 xc=[sum((i in r['Z'])<<j for j,r in enumerate(rows)) for i in range(n)]
 zc=[sum((i in r['X'])<<j for j,r in enumerate(rows)) for i in range(n)]
 single=sorted({0,*xc,*zc,*(a^b for a,b in zip(xc,zc))})
 out += [f'def xs{L} : Array (BitVec {m}) := #[{", ".join(map(str,xc))}]',f'def zs{L} : Array (BitVec {m}) := #[{", ".join(map(str,zc))}]',f'def xc{L} (i : Nat) : BitVec {m} := xs{L}[i]?.getD 0',f'def zc{L} (i : Nat) : BitVec {m} := zs{L}[i]?.getD 0',f'def tree{L} : SyndromeTree := {tree(single)}',f'def allowed{L} (v : BitVec {m}) : Bool := tree{L}.contains v.toNat',f'def row{L} (j : Fin {m}) : Pauli {n} := (l{L}[j.val]?).getD Pauli.zero','']
 out += [f'theorem rows_mem{L} : ∀ j, row{L} j ∈ l{L} := by decide',f'theorem bind_x{L} : ∀ (i : Fin {n}) (j : Fin {m}), (xc{L} i).getLsbD j = (row{L} j).z.getLsbD i := by decide',f'theorem bind_z{L} : ∀ (i : Fin {n}) (j : Fin {m}), (zc{L} i).getLsbD j = (row{L} j).x.getLsbD i := by decide',f'theorem zero_allowed{L} : allowed{L} 0 = true := by decide',f'theorem single_allowed{L} : ∀ (i : Fin {n}) (a : Fin 3), allowed{L} (axiscol xc{L} zc{L} i a) = true := by decide',f'theorem single_nonzero{L} : ∀ (i : Fin {n}) (a : Fin 3), axiscol xc{L} zc{L} i a ≠ 0 := by decide','']
 for i in range(n):
  if L==11 and i>=16:
   out += [f'theorem pair{L}_{i} : ∀ (j : Fin {n}), {i} < j.val → ∀ (a b : Fin 3),',f'    allowed{L} (axiscol xc{L} zc{L} {i} a ^^^ axiscol xc{L} zc{L} j b) = false := by decide','']
  else:
   out += [f'theorem pair{L}_{i} : ∀ (j : Fin {n}) (a b : Fin 3),',f'    (⟨{i}, by decide⟩ : Fin {n}) ≠ j → allowed{L} (axiscol xc{L} zc{L} {i} a ^^^ axiscol xc{L} zc{L} j b) = false := by decide','']
 suffix='_ordered' if L==11 else ''
 condition='i.val < j.val' if L==11 else 'i ≠ j'
 out += [f'theorem pairs{L}{suffix} : ∀ (i j : Fin {n}) (a b : Fin 3), {condition} →',f'    allowed{L} (axiscol xc{L} zc{L} i a ^^^ axiscol xc{L} zc{L} j b) = false := by','  intro i','  rcases i with ⟨i, hi⟩','  match i with']
 for i in range(n):
  if L==7:
   out += [f'  | {i} => exact pair{L}_{i}']
  elif i<16:
   out += [f'  | {i} =>', '    intro j a b h', f'    exact pair{L}_{i} j a b (fun he => (Nat.ne_of_lt h) (congrArg Fin.val he))']
  else:
   out += [f'  | {i} =>', '    intro j a b h', f'    exact pair{L}_{i} j h a b']
 out += [f'  | k + {n} => omega','']
 if L==11:
  out += [f'theorem pairs{L} : ∀ (i j : Fin {n}) (a b : Fin 3), i ≠ j →',f'    allowed{L} (axiscol xc{L} zc{L} i a ^^^ axiscol xc{L} zc{L} j b) = false := by','  intro i j a b hne','  by_cases h : i.val < j.val',f'  · exact pairs{L}_ordered i j a b h','  · have hji : j.val < i.val := by','      have hv : i.val ≠ j.val := fun hv => hne (Fin.ext hv)','      omega','    rw [BitVec.xor_comm]',f'    exact pairs{L}_ordered j i b a hji','']
 out += [f'def certificate{L} : Certificate {n} {m} l{L} where',f'  xc := xc{L}',f'  zc := zc{L}',f'  row := row{L}',f'  row_mem := rows_mem{L}',f'  bind_x := bind_x{L}',f'  bind_z := bind_z{L}',f'  allowed := allowed{L}',f'  zero_allowed := zero_allowed{L}',f'  single_allowed := single_allowed{L}',f'  single_nonzero := single_nonzero{L}',f'  pair_forbidden := pairs{L}','',f'theorem no_small_normalizer{L} (p : Pauli {n}) (hp : Normalizes l{L} p) (hw : p.weight < 4) : p.weight = 0 :=',f'  certificate{L}.no_small_normalizer p hp hw','',f'theorem lower_bound{L} (p : Pauli {n}) (hp : Logical l{L} p) : 4 ≤ p.weight :=',f'  certificate{L}.logical_weight_ge_four p hp','']
out+=['end QLDPC.DistanceProof','']
text='\n'.join(out)
# Chained modules bound transient kernel-reduction memory and enforce serial builds.
# The small proof terms themselves remain ordinary kernel-checked declarations.
headers=['set_option Elab.async false','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','','namespace QLDPC.DistanceProof','open QLDPC.Candidates','']
def emit(name, imports, body):
    content='\n'.join([*(f'import {x}' for x in imports),'',*headers,body,'end QLDPC.DistanceProof',''])
    (root/'QLDPC'/f'{name}.lean').write_text(content)
previous='QLDPC.DistanceCore'
for L,n in [(7,56),(11,88)]:
    start=text.index(f'def xs{L} ')
    pair_start=text.index(f'theorem pair{L}_0 ')
    all_start=text.index(f'theorem pairs{L}_ordered ' if L==11 else f'theorem pairs{L} ')
    end=text.index('def xs11 ') if L==7 else text.index('end QLDPC.DistanceProof')
    name=f'DistanceData{L}'
    emit(name,['QLDPC.Candidates',previous],text[start:pair_start])
    previous=f'QLDPC.{name}'
    for a in range(0,n,8):
        b=min(a+8,n)
        begin=text.index(f'theorem pair{L}_{a} ')
        finish=text.index(f'theorem pair{L}_{b} ') if b<n else all_start
        name=f'DistancePairs{L}_{a//8}'
        emit(name,[previous],text[begin:finish])
        previous=f'QLDPC.{name}'
    name='DistanceCertified7' if L==7 else 'Distance'
    emit(name,[previous],text[all_start:end])
    previous=f'QLDPC.{name}'

