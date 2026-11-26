"""Check only central rational probes using low-order row failure moments."""
from fractions import Fraction
from math import comb
from pathlib import Path
from runpy import run_path

common = run_path(str(Path(__file__).with_name("independent-count.py")))
specified_bad = common["specified_bad"]
rational_node = common["rational_node"]


def probability_bounds(n, d, k, order):
    total = comb(n, k) ** d
    partial = total
    lower, upper = 0, total
    for ell in range(1, order + 1):
        partial += (-1)**ell * comb(n, ell) * specified_bad(n, d, k, ell)
        if ell % 2:
            lower = max(lower, partial)
        else:
            upper = min(upper, partial)
    return Fraction(lower, total), Fraction(upper, total)


def main():
    n, d, r = 36, 12, 10
    degree = n*r//d
    base = [comb(n, k)**d for k in range(degree + 1)]
    lower, upper = zip(*(probability_bounds(n, d, k, 4) for k in range(degree + 1)))
    central = [k for k in range(1, degree) if base[k]**2 <= 4*base[k-1]*base[k+1]]
    assert central == list(range(14, 23))
    probes = []
    for k in central:
        square = (Fraction(base[k-1], base[k+1]) * (lower[k-1]+upper[k-1])
                  / (lower[k+1]+upper[k+1]))
        x = rational_node(square)
        signed_lower = sum((lower[j] if (j-k)%2 == 0 else -upper[j])
                           * Fraction(base[j], base[k]) * x**(j-k)
                           for j in range(degree+1))
        assert signed_lower > 0, k
        probes.append(x)
    assert all(x < y for x, y in zip(probes, probes[1:]))

    # The outside geometric nodes give their signs by strict separation.
    # Compare the extreme outside nodes to the nearest rational probes.
    k = central[0]-1
    assert probes[0]**2 > Fraction(base[k-1], base[k+1]) * upper[k-1]/lower[k+1]
    k = central[-1]+1
    assert probes[-1]**2 < Fraction(base[k-1], base[k+1]) * lower[k-1]/upper[k+1]
    print(f"Checked {len(probes)} rational probes and both joins with order-four probability bounds.")


if __name__ == "__main__":
    main()
