from functools import cache
from math import isqrt
from flint import arb,ctx
ctx.prec=104
PI=arb.pi()

@cache
def angle(n,j):
    return PI*j/n

def threshold(n,k):
    if 2*n<=15*k: return 7
    if n<=10*k: return 5
    return 5 if k<=100 else 6

def entrance(n,k):
    H=isqrt(49*n)//20
    A=threshold(n,k)
    j=H+1
    while True:
        s=angle(n,j).sin()
        if k*s>=A and n*s*s>=arb(6)/5:
            return H,j
        j+=1
        if j>n//2:
            raise ArithmeticError((n,k,"entrance"))

if __name__=='__main__':
    pairs=ranks=0
    J=0
    for n in range(251,1001):
        for k in range(max(7,n//20+1),n//4+1):
            h,j=entrance(n,k)
            J=max(J,j)
            ranks+=j-h-1
            pairs+=1
    print(pairs,ranks,J)
