from fractions import Fraction as F
from math import factorial

def entries(n,j):
    small=[F(0)]+[F(1,factorial(m)) if m<j else F(0) for m in range(1,n+1)]
    big=[F(0)]+[F(1,factorial(m)) if m>=j else F(0) for m in range(1,n+1)]
    g=[F(1)]
    for m in range(1,n+1):
        g.append(sum(small[i]*g[m-i] for i in range(1,m+1)))
    C=[sum(g[m-i]*big[i] for i in range(1,m+1)) for m in range(n+1)]
    return small,big,g,C

def mult(U,V):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*V)] for row in U]

def conv(U,V):
    return [sum(U[i]*V[m-i] for i in range(m+1)) for m in range(len(U))]

def coeffs(n,j,small,big):
    out=[[F(1)]]
    for m in range(1,n+1):
        cur=[F(0)]*(m//j+1)
        for ell in range(1,m+1):
            for k,q in enumerate(out[m-ell]):
                cur[k+(ell>=j)] += (small[ell] or big[ell])*q
        out.append(cur)
    return out[n]

for n in range(3,24):
    for j in range(2,n+1):
        small,big,g,C=entries(n,j)
        A=[[small[r-s+1] if r>=s else F(-1) if r+1==s else F(0) for s in range(n)] for r in range(n)]
        B=[[big[r-s+1] if r>=s else F(0) for s in range(n)] for r in range(n)]
        K=[[g[r]*C[n-s]/g[n]-(C[r-s] if r>=s else 0) for s in range(n)] for r in range(n)]
        assert mult(A,K)==B
        row=coeffs(n,j,small,big)
        powers=[g]
        for k in range(n//j):
            powers.append(conv(powers[-1],C))
        d=n//j
        gram=[[sum(powers[a][n-1-i]*sum(big[i-r+1]*powers[b][r] for r in range(i+1)) for i in range(n)) for b in range(d)] for a in range(d)]
        assert gram==[[row[a+b+1] if a+b+1<=d else 0 for b in range(d)] for a in range(d)]
        if j>=3 and n>=j+2:
            assert C[j+1]**2-C[j]*C[j+2] < 0
print("252 rational matrix and Gram identities checked.")
