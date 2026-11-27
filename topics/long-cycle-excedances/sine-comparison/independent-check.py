"""Independent rational check using direct powers of the primitive majorant."""
from fractions import Fraction as R
from functools import cache
from math import ceil, factorial, isqrt

G = 1 << 52
U = R(6, 5)
P = 67
SLABS = [(4, 6), (6, 10), (10, 16), (16, 22), (22, 28), (28, 34),
         (34, 40), (40, 44), (44, 48)]
ODD = list(range(-P, P + 1, 2))


def poly_mul(a, b, top):
    result = {}
    for i, u in a.items():
        for j, v in b.items():
            if i+j <= top:
                result[i+j] = result.get(i+j, 0) + u*v
    return result


@cache
def lattice(c):
    kernel = {p: ceil(G * (1+c*(p*p-1))**-96) for p in ODD}
    assert 191*c*P*P > 1-c
    first_tail = (1+c*(P*P-1))**-95 / (190*c)
    mass_tail = first_tail/P
    mass = R(sum(kernel.values()), G) + mass_tail
    first = R(sum(abs(p)*val for p, val in kernel.items() if abs(p) >= 3), G)
    star = max(R(sum(ceil(R(val, abs(a-p))) for p, val in kernel.items() if p != a), G)
               for a in range(1,P+3,2)) + mass_tail/2
    return tuple(R(ceil(G*z),G) for z in (mass, first+first_tail, star))


def all_terms(top, K, X, A):
    L = {}
    for i in range(4,top+1):
        g = R(1) if i == 4 else R(i-1,4)
        if i == 4:
            v = R(1)
        elif i <= 8:
            v = 1/(g-R(1,K))-4/R(i)+(R(1,4*K) if i == 8 else 0)
        else:
            v = (R(1,4)+R(1,K))/(2*factorial((i-1)//4))
        L[i] = ceil(G*v*lattice((g-R(1,K))*U/(192*X))[2]/A)
    # Each power has denominator G**j. Divide by j! and round just its output.
    power = L
    multi = [0]*(top+1)
    for j in range(2,top//4+1):
        power = poly_mul(power, L, top)
        for b, coefficient in power.items():
            multi[b] += ceil(R(coefficient, G**(j-1)*factorial(j)))
    all_coeff = [R(int(b == 0)*G+L.get(b,0)+multi[b],G) for b in range(top+1)]
    return all_coeff, [R(v,G) for v in multi]


def e(g):
    if g < 1:
        return R(4,7)
    if g < 2:
        return R(453,1000)
    j = min(40,int(g))
    return min(R(4,7)-(R(1,2) if j == 2 else R(547,1000)),
               R(j+1,2*j*factorial(j)))


def bound(lo, X, high):
    K = 10000//X
    A0 = R(isqrt((16*12000)//(X*X)),4)
    if high:
        A0 = max(A0,R(10))
    coeff, multi = all_terms(5*X if high else 240, K, X, A0)
    Pcost = R(0) if high else R(1,10000)
    V = B = J = R(0)
    if high:
        Kmass=lattice(U/(192*X))[0]
        singleton=lattice((R(lo-1)-R(1,K))*U/(192*X))[2]
        J += Kmass*singleton / (A0**2*2*factorial(lo-1))
    for b, q in enumerate(coeff):
        h = R(b,4)
        g = max(R(1),R(b,5)) if b else R(0)
        if not high:
            Pcost += 2*e(lo-h)*q
        mass, moment, _ = lattice(max(R(1,X),1-h/lo)*U/192)
        if g+1 <= X and b <= 5*X:
            value = moment + (2 if high and b else 0)
            V += (R(4,7) if lo-h >= 2 else R(1))*q*value
        if g+1 <= X+R(1,K) and b < 5*X:
            v = R(1) if lo-h <= 2 else R(1,2*factorial(ceil(lo-h)-1))
            B += v*mass*q/A0
            if h > lo-1:
                if high:
                    J += A0*X*mass*multi[b]/U
                else:
                    J += 10*X*mass*q/U
    carrier = R(1094,1000) if high else R(47*97,10000)
    margin = carrier-Pcost-V-B-J
    assert margin > (R(473268,10**6) if high else R(291701,10**6))
    print(lo, X, 'large' if high else 'small',
          *(ceil(z*10**6) for z in (Pcost,V,B,J)), int(margin*10**6), flush=True)


for lo, X in SLABS:
    bound(lo, X, True)
    if X >= 16:
        bound(lo, X, False)
