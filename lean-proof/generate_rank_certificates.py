import json, pathlib
root=pathlib.Path(__file__).resolve().parent
lines=['import QLDPC.Rank','import QLDPC.Candidates','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace QLDPC.Candidates','']
for L in [7,11]:
 d=json.loads((root/'data'/f'xyz-degree-five-cube-L{L}.json').read_text())
 n=d['n']; rows=[sum(1<<x for x in s['X'])+(sum(1<<z for z in s['Z'])<<n) for s in d['checks']['S']]; m=len(rows)
 b=[(v,1<<i) for i,v in enumerate(rows)]; piv=[]; r=0
 for j in range(2*n):
  k=next((k for k in range(r,m) if b[k][0]>>j&1),None)
  if k is None:continue
  b[r],b[k]=b[k],b[r]
  for k in range(m):
   if k!=r and b[k][0]>>j&1:b[k]=(b[k][0]^b[r][0],b[k][1]^b[r][1])
  piv.append(j);r+=1
 basis=b[:r];sourcecoeff=[sum(((v>>p)&1)<<j for j,p in enumerate(piv)) for v in rows]
 for v,c in basis: assert v==__import__('functools').reduce(int.__xor__,(rows[i] for i in range(m) if c>>i&1),0)
 for v,c in zip(rows,sourcecoeff): assert v==__import__('functools').reduce(int.__xor__,(basis[i][0] for i in range(r) if c>>i&1),0)
 def decl(name,typ,vals):
  lines.extend([f'def {name}{L} : {typ} := [',',\n'.join('  '+str(v) for v in vals),']',''])
 decl('basisList',f'List (Pauli {n})',[f'⟨{v&((1<<n)-1)}, {v>>n}⟩' for v,c in basis])
 decl('fromSourceMasks',f'List (BitVec {m})',[c for v,c in basis])
 decl('toBasisMasks',f'List (BitVec {r})',sourcecoeff)
 decl('pivotList',f'List Nat',piv)
 lines.extend([f'def source{L} (i : Fin {m}) : Pauli {n} := l{L}.get ⟨i.val, by simpa only [l{L}_row_count] using i.isLt⟩',f'def basis{L} (i : Fin {r}) : Pauli {n} := basisList{L}.get i',f'def fromSource{L} (i : Fin {r}) (j : Fin {m}) : Bool := (fromSourceMasks{L}.get i).getLsbD j',f'def toBasis{L} (i : Fin {m}) (j : Fin {r}) : Bool := (toBasisMasks{L}.get i).getLsbD j',f'def pivots{L} (i : Fin {r}) : Nat := pivotList{L}.get i',''])
 # Obtain a pure-X dual satisfying all row z constraints and witness anticommutation.
 wz=sum(1<<z for z in d['distance']['P']['witness']['Z'])
 eq=[(v>>n,0) for v in rows]+[(wz,1)]
 pvs=[]; rr=0
 for j in range(n):
  k=next((k for k in range(rr,len(eq)) if eq[k][0]>>j&1),None)
  if k is None:continue
  eq[rr],eq[k]=eq[k],eq[rr]
  for k in range(len(eq)):
   if k!=rr and eq[k][0]>>j&1:eq[k]=(eq[k][0]^eq[rr][0],eq[k][1]^eq[rr][1])
  pvs.append(j);rr+=1
 assert all(v or not a for v,a in eq)
 dual=sum(a<<j for j,(_,a) in zip(pvs,eq[:rr]))
 assert all((dual&(v>>n)).bit_count()%2==0 for v in rows)
 assert (dual&wz).bit_count()%2==1
 lines.extend([f'def dual{L} : Pauli {n} := ⟨{dual}, 0⟩',''])
 print(L,'rank',r,'dual X',[i for i in range(n) if dual>>i&1])
lines.extend(['end QLDPC.Candidates',''])
(root/'QLDPC/RankData.lean').write_text('\n'.join(lines))
