from fractions import Fraction as F
from itertools import combinations
import random, subprocess

def vertex(rows, n):
    if n == 0:
        return all(r[0] <= 0 for r in rows)
    for selected in combinations(rows, n):
        a = [[F(x) for x in r[1:]] + [F(-r[0])] for r in selected]
        for j in range(n):
            pivot = next((i for i in range(j,n) if a[i][j]), None)
            if pivot is None: break
            a[j], a[pivot] = a[pivot], a[j]
            d = a[j][j]; a[j] = [x/d for x in a[j]]
            for i in range(n):
                if i != j:
                    d = a[i][j]; a[i] = [x-d*y for x,y in zip(a[i],a[j])]
        else:
            x = [a[i][-1] for i in range(n)]
            if all(r[0] + sum(c*v for c,v in zip(r[1:],x)) <= 0 for r in rows):
                return True
    return False

cases=[]
def add(n, rows, result): cases.append((n,rows,result))
add(0,[],0); add(4,[],0)
add(0,[[-1],[0]],0); add(0,[[1]],1)
add(1,[[1,-1],[0,1]],1)
add(1,[[1,-2],[-1,2]],0)
add(1,[[2,-2],[-2,2]],0)
add(2,[[3,1,0]],0)
add(2,[[1,-1,-1],[0,1,0],[0,0,1]],1)
add(3,[[1,-1,0,0],[-2,1,0,0],[0,0,0,0]],0)
big=10**90+37
add(1,[[big,-2*big],[-big,2*big]],0)
add(1,[[big,-big],[0,big]],1)
rng=random.Random(20261111)
# Box bounds make every nonempty feasible polyhedron have a vertex.
for n in range(1,4):
    for k in range(180):
        rows=[]
        for j in range(n):
            for sign in [-1,1]:
                r=[-4]+[0]*n; r[j+1]=sign; rows.append(r)
        rows += [[rng.randint(-6,6)]+[rng.randint(-4,4) for _ in range(n)] for _ in range(rng.randint(1,7))]
        expected=0 if vertex(rows,n) else 1
        add(n, rows, expected)
        # Positive scaling, duplicate rows, row permutation preserve feasibility.
        if k%15==0:
            changed=[list(r) for r in rows]
            changed=[[x*(i+2) for x in r] for i,r in enumerate(changed)]
            changed += changed[:2]; rng.shuffle(changed)
            add(n,changed,expected)
text=''.join(f'{len(rows)} {n}\n'+''.join(' '.join(map(str,r))+'\n' for r in rows) for n,rows,_ in cases)
p=subprocess.run(['./build/driver'],input=text,text=True,capture_output=True,timeout=90)
assert p.returncode==0, p.stderr
answers=list(map(int,p.stdout.split()))
assert len(answers)==len(cases)
for i,(got,(_,rows,want)) in enumerate(zip(answers,cases)):
    assert got==want,(i,rows,want,got)
print(f'{len(cases)} exact cases passed; {answers.count(0)} feasible, {answers.count(1)} infeasible; input preserved')