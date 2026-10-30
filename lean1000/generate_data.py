#!/usr/bin/env python3
"""Generate literals and proof certificates; Lean checks their semantics.
Code/witnesses: hirobumii PR3863. Structural strategy: Henryk Soboń.
No Python result is installed as an axiom or unproved Lean premise.
"""
from pathlib import Path
import json, hashlib

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'source.json'
raw = SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'fdc1e71bfd9a588b39f545882a93b5b316582ecdd157451bd03c7411219b842b'
data = json.loads(raw)

def mul(x,y):
    return (x%5 + pow(2,x//5,5)*(y%5))%5 + 5*((x//5+y//5)%20)
def inv(x):
    return next(y for y in range(100) if mul(x,y)==mul(y,x)==0)
a,b = [5,6,36],[5,16,19]
full = {s:[[] for _ in range(300)] for s in ('X','Z')}
for k in range(3):
    for j in range(3):
        for u in range(100):
            q=100*(3*k+j)+u
            for r in (100*j+u,100*j+mul(inv(a[k]),u)): full['X'][r].append(q)
            for r in (100*k+u,100*k+mul(u,b[j])): full['Z'][r].append(q)
for u in range(100):
    for j in range(3):
        for r in (100*j+u,100*j+mul(u,inv(b[j]))): full['X'][r].append(900+u)
    for k in range(3):
        for r in (100*k+u,100*k+mul(a[k],u)): full['Z'][r].append(900+u)
for rows in full.values():
    for row in rows: row.sort()

def mask(s):
    z=0
    for q in s:z^=1<<q
    return z
def separator(rows, witness):
    piv={}
    for row,rhs in [(row,0) for row in rows]+[(witness,1)]:
        m=mask(row)
        while m:
            q=m.bit_length()-1
            if q not in piv: piv[q]=(m,rhs);break
            m^=piv[q][0];rhs^=piv[q][1]
        assert m or not rhs
    v=0
    for q,(m,rhs) in sorted(piv.items()):
        if ((m&v).bit_count()%2)^rhs:v|=1<<q
    assert all((mask(row)&v).bit_count()%2==0 for row in rows)
    assert (mask(witness)&v).bit_count()%2==1
    return [q for q in range(1000) if v>>q&1]

def lean(x, arrays=0):
    if isinstance(x,list):return ('#[' if arrays else '[')+','.join(lean(z,max(0,arrays-1)) for z in x)+']'
    return str(x)
out=['import Qldpc1000.Core','namespace Qldpc1000.Data',
     '/- Generated from the exact published JSON and independently reconstructed full rows. -/']
for sector in ('X','Z'):
    rows=data['checks'][sector]
    assert rows==[row for r,row in enumerate(full[sector]) if r%100!=99]
    out += [f'def stored{sector} : List (List Nat) := '+lean(rows),
            f'def full{sector} : Array (List Nat) := '+lean(full[sector],1)]
    kind=[(q//100)%3 if sector=='X' else q//300 for q in range(900)]+[3]*100
    out += [f'def kinds{sector} : Array Nat := '+lean(kind,1)]
    blockrows=[];recipes=[];cols=[];vneighbors=[];cneighbors=[]
    for block in range(3):
        localrows=full[sector][100*block:100*(block+1)]
        # XOR odd-phase rows equals XOR the50 even-phase retained rows.
        marker=[q for q in range(1000) if kind[q] in (block,3)]
        assert mask(marker)==__import__('functools').reduce(int.__xor__,[mask(localrows[r]) for r in range(100) if r//5%2],0)
        blockrows.append(localrows+[marker])
        recipe=[]
        for r in range(100):
            recipe.append([localrows[r]] if r!=99 else localrows[:99])
        recipe.append([localrows[r] for r in range(100) if r//5%2==0])
        recipes.append(recipe)
        columns=[sum(1<<r for r,row in enumerate(localrows+[marker]) if q in row) for q in range(1000)]
        cols.append(columns)
        vneighbors.append([[q for q in row if kind[q]==block] for row in localrows])
        cneighbors.append([[q for q in row if kind[q]==3] for row in localrows])
    out += [f'def blocks{sector} : Array (Array (List Nat)) := '+lean(blockrows,2),
            f'def recipes{sector} : Array (Array (List (List Nat))) := '+lean(recipes,2),
            f'def columns{sector} : Array (Array Nat) := '+lean(cols,2),
            f'def vvNeighbors{sector} : Array (Array (List Nat)) := '+lean(vneighbors,2),
            f'def ccNeighbors{sector} : Array (Array (List Nat)) := '+lean(cneighbors,2),
            f'def witness{sector} : List Nat := '+lean(data['distance'][sector]['witness']),
            f'def separator{sector} : List Nat := '+lean(separator(rows,data['distance'][sector]['witness']))]
out += ['end Qldpc1000.Data']
(ROOT/'Qldpc1000/Data.lean').write_text('\n\n'.join(out)+'\n')
print('Generated',ROOT/'Qldpc1000/Data.lean')
