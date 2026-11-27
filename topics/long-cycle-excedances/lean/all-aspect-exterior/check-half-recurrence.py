from math import comb
from fractions import Fraction
from hashlib import sha256

pairs = [(10000,5000),(10001,5001),(10000,5002),(10008,5000)]
samples = range(1,51)
needed = set()
for n,k in pairs:
    for r in (n,n+1):
        needed.update([r, *range(k,r-k+1)])
current = [1]+[0]*49
cycles = {}
for r in range(2, max(needed)+1):
    current = [(j+1)*c+(r-1-j)*(current[j-1] if j else 0)
               for j,c in enumerate(current)]
    if r in needed:
        cycles[r] = [0,*current]

def mul(a,b,p):
    return sum(cycles[a][h]*cycles[b][p-h] for h in range(1,p))

def coeff(r,k,p):
    result = cycles[r][p]
    for a in range(k,r//2+1):
        result += comb(r,a)//(2 if 2*a == r else 1)*mul(a,r-a,p)
    return result

assert Fraction(100,99)*(1+Fraction(8,3)*Fraction(151,100))*(Fraction(1,200)+Fraction(29,500)) == Fraction(2639,8250)
assert Fraction(8,25)-Fraction(2639,8250) == Fraction(1,8250)
assert 300*Fraction(29,500)**2 > 1
for n,k in pairs:
    sizes=[0]*3
    out=sha256()
    for p in samples:
        u,v=coeff(n,k,p),coeff(n+1,k,p)
        w=v-p*u-(n+1-p)*coeff(n,k,p-1)
        assert 0 <= 25*w < 8*u
        m=n+1-k
        if m>=k:
            assert w == comb(n,k-1)*mul(k,m,p)
        else:
            assert w == 0
        for i,c in enumerate((u,v,w)):
            data=c.to_bytes((c.bit_length()+7)//8, 'big')
            out.update(len(data).to_bytes(8,'big')+data)
            sizes[i] += c>0
    print(n,k,50,sizes,out.hexdigest())
