"""Compare the first-block recursion with the ordered gap-product coefficients."""
from math import comb
from pathlib import Path
import runpy

rows = runpy.run_path(str(Path(__file__).with_name("check.py")))["rows"]


def mul(a, b, nmax):
    return [sum(comb(n, i) * a[i] * b[n-i] for i in range(n+1))
            for n in range(nmax+1)]


def verify():
    nmax = 60
    count = 0
    for j in range(2, 13):
        # Factorials are absorbed in the working vectors, so EGF multiplication
        # is binomial convolution. T counts an ordered sequence of short blocks.
        short = [1] + [0] * nmax
        for n in range(1, nmax+1):
            short[n] = sum(comb(n, a) * short[n-a]
                           for a in range(1, min(n, j-1)+1))
        long = [int(n >= j) for n in range(nmax+1)]
        gap = mul(short, long, nmax)
        cols = [short]
        for _ in range(nmax//j):
            cols.append(mul(cols[-1], gap, nmax))
        literal = rows(j, nmax)
        for n, original in enumerate(literal):
            reconstructed = [col[n] for col in cols]
            if (reconstructed[:len(original)] != original
                    or any(reconstructed[len(original):])
                    or any(c <= 0 for c in original)):
                raise ArithmeticError((j, n))
            count += 1
    print(f"{count} complete rows matched the independent gap product.")


if __name__ == "__main__":
    verify()
