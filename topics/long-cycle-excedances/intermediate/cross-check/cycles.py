"""Build selected coefficient vectors directly by the cycle containing the least label."""
from functools import cache
from math import comb
from flint import fmpz_poly
from verify import reduced_rows, WIDTH

def eulerian_rows(limit):
    x = fmpz_poly([0,1])
    old = fmpz_poly([1])
    yield old
    for m in range(2,limit+1):
        old = (old + (m-1)*x*old + x*(1-x)*old.derivative()).truncate(WIDTH)
        yield old

def check(rows,n,k):
    # A length-d cycle, started with its greatest label, has one return
    # ascent and the internal ascents of a word on the other d-1 labels.
    @cache
    def from_cycle(m):
        result = rows[m-2]
        for ell in range(k,m-k+1):
            weight = comb(m-1,ell-1)
            tail = rows[ell-2].mul_low(from_cycle(m-ell),WIDTH-1)
            result = result + (weight*tail).left_shift(1)
        return result.truncate(WIDTH)
    _,a,b = list(reduced_rows(k,n))[-1]
    assert a == from_cycle(n) and b == from_cycle(n+1)
    print(n,k,WIDTH*2,'matching coefficients',flush=True)

if __name__=='__main__':
    if not __debug__: raise SystemExit('Use Python with assertions enabled.')
    examples = [(251,13),(251,33),(252,63),(401,100),(421,67),(999,249)]
    rows = list(eulerian_rows(max(n for n,k in examples)))
    for n,k in examples: check(rows,n,k)
