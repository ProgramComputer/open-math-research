"""Reconstruct and compare the two exact signed odd-lattice linear tables."""

from fractions import Fraction as F
from functools import cache
from math import ceil, factorial, isqrt
from pathlib import Path


SLABS = ((4, 6), (6, 10), (10, 16), (16, 22), (22, 28),
         (28, 34), (34, 40), (40, 44), (44, 48))
U = F(6, 5)


def floor_mass(K, i):
    if i == 4:
        return F(1), F(1)
    y = F(i-1, 4)
    if i <= 8:
        return y, 1/(y-F(1,K))-F(4,i)+(F(1,4*K) if i==8 else 0)
    return y, (F(1,4)+F(1,K))/(2*factorial((i-1)//4))


@cache
def star(shape, precision, cutoff):
    scale = 1 << precision
    odd = range(-cutoff, cutoff+1, 2)
    # Include both nearest external centers. This avoids assuming reflection
    # in the computational witness for the full finite signed head.
    weights = {q: ceil(scale*(1+shape*(q*q-1))**-96) for q in odd}
    assert 3*shape*cutoff**2 >= 1
    tail = (1+shape*(cutoff*cutoff-1))**-95/(190*shape*cutoff)
    if precision == 56:
        head = max(sum(ceil(F(weights[q], abs(q-a))) for q in odd if q!=a)
                   for a in range(-cutoff-2, cutoff+3, 2))
        first_tail = ceil(scale*tail*cutoff)
        mass_tail = ceil(F(first_tail, cutoff))
        upper = F(head+ceil(F(mass_tail,2)), scale)
    else:
        head = max(sum(ceil(F(weights[q], abs(q-a))) for q in odd if q!=a)
                   for a in range(-cutoff-2, cutoff+3, 2))
        upper = F(ceil(head+scale*tail/2), scale)
    return upper


def load_definitions(path, stop=None):
    content = path.read_text()
    namespace = {'__file__': str(path), '__name__': 'supplied_checked_functions'}
    if stop:
        content = content[:content.index(stop)]
    exec(compile(content, str(path), 'exec'), namespace)
    return namespace


def main(reference):
    pinned = load_definitions(reference/'degree-blocks'/'verify_degree_blocks.py', "if __name__ ==")
    direct = load_definitions(reference/'sine-comparison'/'independent-check.py', "def bound(")
    for lo, X in SLABS:
        K = 10000//X
        A = F(isqrt(192000)//X,4)
        assert K >= 208 and A*A*X*X <= 12000
        table = []
        for i, g0, m0 in pinned['degree_masses'](K, 60):
            g, m = floor_mass(K,i)
            assert (g,m)==(g0,m0)
            c = (g-F(1,K))*U/(192*X)
            star63 = star(c,56,63)
            star67 = star(c,52,67)
            assert star63 == pinned['stars'](c)[0]
            assert star67 == direct['lattice'](c)[2]
            l63 = ceil((1<<56)*m*star63/A)
            l67 = ceil((1<<52)*m*star67/A)
            assert l63 == pinned['up'](m*pinned['stars'](c)[0]/A)
            assert l67 == ceil((1<<52)*m*direct['lattice'](c)[2]/A)
            table.append((i,l63,l67))
        assert len(table) == 237
        print(lo,X,K,A,*(f"{s}/{1<<p}" for s,p in zip(table[0][1:],(56,52))),flush=True)


if __name__ == "__main__":
    main(Path(__file__).resolve().parents[2])
