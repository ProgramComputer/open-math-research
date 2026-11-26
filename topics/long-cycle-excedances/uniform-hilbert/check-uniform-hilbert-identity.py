"""Independent Gaussian-rational finite-pole replay, including derivatives."""
from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class G:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, b):
        return G(self.re+b.re, self.im+b.im)

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, b):
        return self+-b

    def __mul__(self, b):
        return G(self.re*b.re-self.im*b.im, self.re*b.im+self.im*b.re)

    def inverse(self):
        norm = self.re*self.re+self.im*self.im
        return G(self.re/norm, -self.im/norm)


@dataclass(frozen=True)
class D:
    value: G = G()
    derivative: G = G()

    def __add__(self, b):
        return D(self.value+b.value, self.derivative+b.derivative)

    def __sub__(self, b):
        return D(self.value-b.value, self.derivative-b.derivative)

    def __mul__(self, b):
        return D(self.value*b.value, self.derivative*b.value+self.value*b.derivative)

    def inverse(self):
        inv = self.value.inverse()
        return D(inv,-(inv*inv*self.derivative))


ZERO = D()
ONE = D(G(Q(1)))
N = 20


def scalar(v):
    return D(G(Q(v)))


def convolve(a,b):
    result = [ZERO]*(N+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:N+1-i]):
            result[i+j] = result[i+j]+x*y
    return result


def check(k, poles, sine, cosine):
    d = [Q(1)]+[Q(0)]*(k-1)
    for n in range(k,N+1):
        d.append(sum(d[:n-k+1])/n)
    b = [Q(0)]*k+[d[k]]+[d[n]-d[n-1] for n in range(k+1,N+1)]
    powers = {}
    for pole in poles:
        z = D(G(cosine,pole*sine),G(-sine,pole*cosine)).inverse()
        powers[pole] = [ONE]
        for _ in range(N):
            powers[pole].append(powers[pole][-1]*z)

    correct = [ONE]+[ZERO]*N
    one_pole = [ZERO]*(N+1)
    for pole in poles:
        row = [scalar(d[n])*p for n,p in enumerate(powers[pole])]
        correct = convolve(correct,row)
        for n in range(1,N+1):
            one_pole[n] = one_pole[n]+row[n]

    collected = [ZERO]*(N+1)
    for a in poles:
        product = [ONE]+[ZERO]*N
        for q in poles:
            if q==a:
                continue
            difference = D(G(Q(0),(q-a)*sine),G(Q(0),(q-a)*cosine)).inverse()
            ratio = [ONE]+[ZERO]*(k-1)
            ratio += [scalar(b[s])*powers[q][s-1]*difference for s in range(k,N+1)]
            product = convolve(product,ratio)
        product[0] = product[0]-ONE
        row = [ZERO]+[scalar(d[n])*powers[a][n] for n in range(1,N+1)]
        piece = convolve(row,product)
        collected = [x+y for x,y in zip(collected,piece)]

    for n in range(1,N+1):
        if collected[n] != correct[n]-one_pole[n]:
            raise ArithmeticError((k,poles,n))


if __name__ == "__main__":
    check(3,(-5,-3,-1,1,3,5),Q(3,5),Q(4,5))
    check(4,(-7,-3,1,5),Q(5,13),Q(12,13))
    print("Exact finite-pole identity and angular derivative agree in all 40 degrees.")
