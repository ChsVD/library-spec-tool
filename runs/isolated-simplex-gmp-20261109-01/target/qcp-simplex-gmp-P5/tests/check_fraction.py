"""Self-authored exact arithmetic oracle; no external SMT tests or software."""
from fractions import Fraction
import random,subprocess
rng=random.Random(20261106)
cli='./build/arith_cli'
count=0
def check(op,an,ad,bn,bd):
 global count
 a,b=Fraction(an,ad),Fraction(bn,bd)
 if op=='/' and not b:return
 expected={'c':lambda:(a>b)-(a<b),'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b,'/':lambda:a/b}[op]()
 s=str(expected) if op=='c' else f'{expected.numerator}/{expected.denominator}'
 p=subprocess.run([cli,op,str(an),str(ad),str(bn),str(bd)],capture_output=True,text=True,timeout=10)
 assert p.returncode==0 and p.stdout.strip()==s,(op,an,ad,bn,bd,p.stdout,p.stderr,s)
 count+=1
vals=[0,1,-1,2**32-1,2**32,2**32+1,-2**64,2**64-1,2**64+1]
for k in [31,32,33,63,64,65,127,128,256,512]:
 for d in [-1,0,1]:vals.append(2**k+d)
for i,v in enumerate(vals):
 for op in '+-*/c': check(op,v,-(2**(i%8*32)+1),2**(i%5*32)+1,2**32)
for _ in range(160):
 bits=rng.choice([8,32,64,128,256,512,1024]); an=rng.getrandbits(bits)*rng.choice([-1,1]);bn=rng.getrandbits(bits)*rng.choice([-1,1]);ad=(rng.getrandbits(bits)or 1)*rng.choice([-1,1]);bd=(rng.getrandbits(bits)or 1)*rng.choice([-1,1])
 for op in '+-*/c':check(op,an,ad,bn,bd)
for op in '+-*/c':check(op,7*2**512,3*2**512,-11*2**512,13*2**512)
print(f'Python Fraction oracle passed: {count} independent CLI comparisons')
