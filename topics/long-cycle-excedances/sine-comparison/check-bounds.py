"""Rational enclosures for the two-angle adjacent sine comparison."""
from fractions import Fraction as F
from math import ceil, factorial, isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'paired-residues'))
import check as paired

prev = paired.prev
B = 4
U = F(6, 5)
SLABS = [(4,6),(6,10),(10,16),(16,22),(22,28),(28,34),(34,40),(40,44),(44,48)]

def regular_numerator(g):
    # k² |b_s| for s>k and s/k>=g.
    if g <= 2:
        return F(1)
    j = ceil(g)-1
    return F(1,2*factorial(j))

def low_angle(lo,X):
    K = 10000//X
    A = F(isqrt(192000)//X,4)
    assert A >= F(9,4) and A < 10 and A*A*X*X <= 12000
    Q,_ = paired.coefficients(K,lo,X,A,240)
    # Apply the existing tail bound to the unmarked principal value terms.
    principal_value = F(1,10000)
    nonprincipal_value = regular = jump = F(0)
    for b, coeff in enumerate(Q):
        qb = F(coeff, paired.G)
        h = F(b,B)
        g = max(F(1),F(b,B+1)) if b else F(0)
        principal_value += 2*paired.eps(lo-h)*qb
        # For r >= k, T+r=n and hence b<=5X and g+1<=X.
        y = max(F(1,X),1-h/lo)
        c = y*U/192
        if b <= 5*X and g+1 <= X:
            old_weight = F(4,7) if lo-h >=2 else F(1)
            nonprincipal_value += old_weight*prev.first_nonprincipal(c)*qb
        # For s=n+1-T>=k, T/k<=X-1+1/k and b<5X.
        if b < 5*X and g+1 <= X+F(1,K):
            mass = prev.mass(c)
            regular += regular_numerator(max(1,lo-h))*mass*qb/A
            # An atom s=k needs b/4>=T/k=n/k-1+1/k>lo-1.
            if b>B*(lo-1):
                jump += (10*X/U)*mass*qb
    carrier = F(47,100)*F(97,100)
    return principal_value, nonprincipal_value, regular, jump, carrier

def high_angle(lo,X):
    K=10000//X
    A=max(F(10),F(isqrt(192000)//X,4))
    Q,_=paired.coefficients(K,lo,X,A,5*X)
    L = {i:paired.up(mass*prev.stars((g-F(1,K))*U/(192*X))[0]/A)
         for i,g,mass in prev.degree_masses(K,(5*X)//B)}
    cstar=(F(lo-1)-F(1,K))*U/(192*X)
    singleton = F(1,2*factorial(lo-1))*prev.stars(cstar)[0]*prev.mass(U/(192*X))/(A*A)
    old=regular=F(0)
    atom=singleton
    for b,coeff in enumerate(Q):
        if not coeff: continue
        q=F(coeff,paired.G)
        h=F(b,B)
        g=max(F(1),F(b,B+1)) if b else F(0)
        y=max(F(1,X),1-h/lo)
        c=y*U/192
        if g+1<=X:
            weight=F(4,7) if lo-h>=2 else F(1)
            old+=weight*(prev.first_nonprincipal(c)+(2 if b else 0))*q
        if b<5*X and g+1 <=X+F(1,K):
            mass=prev.mass(c)
            regular+=regular_numerator(max(1,lo-h))*mass*q/A
            if b>B*(lo-1):
                atom+=A*X/U*mass*(q-F(L.get(b,0),paired.G))
    return old, regular, atom, 2*F(547,1000)


def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    paired.global_bounds()
    for arm, slabs, bound, minimum in (
        ('large', SLABS, high_angle, F(473268,10**6)),
        ('small', SLABS[2:], low_angle, F(291701,10**6)),
    ):
        for lo, hi in slabs:
            *costs, carrier = bound(lo, hi)
            margin = carrier - sum(costs)
            assert margin > minimum, (arm, lo, hi, margin)
            print(arm, lo, hi, *(ceil(10**6 * cost) for cost in costs), int(10**6 * margin))


if __name__ == '__main__':
    main()
