"""Exact reduced prefixes from single-cycle Eulerian polynomials."""
from math import comb, factorial
from flint import fmpz_poly

def eulerian(max_n, width):
    rows = [None, fmpz_poly([1])]
    for n in range(2,max_n+1):
        prev = rows[-1]
        rows.append(fmpz_poly([
            (j+1)*prev[j]+(n-j)*prev[j-1] for j in range(min(n,width))
        ]))
    return rows


def update(rows, cyc, max_n, k, width):
    powers = [fmpz_poly([1])]
    factors = [1]
    fac = factorial(k)
    for h in range(1,max_n//k+1):
        powers.append(powers[-1].mul_low(cyc[k-1],width))
        factors.append(factorial(h*k)//(fac**h*factorial(h)))
    for n in range(max_n,k-1,-1):
        result = rows.get(n,fmpz_poly())
        if n%k==0:
            h = n//k
            result += factors[h]*powers[h].left_shift(h-1)
        for h in range(1,(n-k-1)//k+1):
            result += comb(n,h*k)*factors[h]*powers[h].mul_low(rows[n-h*k],width).left_shift(h)
        rows[n] = result.truncate(width)


def next_rows(k, limit, cycle, width):
    t=fmpz_poly([0,1])
    one=fmpz_poly([1])
    rows={k:cycle[k-1]}
    for n in range(k,limit):
        old=rows[n]
        result=(one+(n-1)*t)*old+t*(one-t)*old.derivative()
        m=n+1-k
        if m>=k:
            result+=comb(n,k-1)*t*cycle[k-1].mul_low(rows[m],width-1)
        rows[n+1]=result.truncate(width)
    return rows
