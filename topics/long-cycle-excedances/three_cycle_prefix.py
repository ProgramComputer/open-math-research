"""Exact rolling cutoff for excedance prefixes in the three-cycle band."""
from math import comb
from time import perf_counter
from flint import fmpz_poly


def eulerian_prefixes(limit, width):
    result = {1: fmpz_poly([1])}
    previous = [1]
    for n in range(2, limit + 1):
        current = [0] * min(n, width)
        for j, coefficient in enumerate(previous):
            current[j] += (j + 1) * coefficient
            if j + 1 < len(current):
                current[j + 1] += (n - 1 - j) * coefficient
        result[n] = fmpz_poly(current)
        previous = current
    return result


def band_prefixes(limit, width, first_n=192, first_k=3):
    """Yield (k, {n: Q_n prefix}) in descending k, never summing over cycle lengths."""
    eulerian = eulerian_prefixes(limit - 1, width)
    empty = fmpz_poly()
    t = fmpz_poly([0, 1])
    squares = {}
    cubes = {}
    for k in range(limit // 2, first_k - 1, -1):
        top = min(4 * k, limit)
        base = eulerian[k-1]
        two_base = base.mul_low(base, width)
        choose = {2*k: comb(2*k, k)}
        for n in range(2*k+1, top+1):
            choose[n] = choose[n-1] * n // (n-k)
        next_cubes = {}
        for n in range(3 * k, top + 1):
            coefficient = cubes.get(n, empty)
            if n == 3*k:
                coefficient += choose[n] * choose[2*k] // 6 * two_base.mul_low(base, width)
            else:
                if n >= 3*k + 2:
                    coefficient += choose[n] * base.mul_low(squares[n-k], width)
                repeated = choose[n] * choose[n-k] // 2
                coefficient += repeated * two_base.mul_low(eulerian[n-2*k-1], width)
            next_cubes[n] = coefficient

        next_squares = {2*k: (choose[2*k]//2)*two_base}
        for n in range(2*k+1, top+1):
            next_squares[n] = squares.get(n, empty) + choose[n] * base.mul_low(eulerian[n-k-1], width)

        squares, cubes = next_squares, next_cubes
        lo = max(first_n, 3*k-1)
        rows = {}
        for n in range(lo, top+1):
            rows[n] = (eulerian[n-1] + t.mul_low(squares[n], width)
                       + (t*t).mul_low(cubes.get(n, empty), width))
        if 4*k <= limit and 4*k >= lo:
            # The new row paired with n=4k-1 has four k-cycles.
            n = 4*k
            multiplicity = choose[n]*choose[3*k]*choose[2*k]//24
            rows[n] += multiplicity * (t*t*t).mul_low(two_base.mul_low(two_base, width), width)
        if rows:
            yield k, rows


def direct(n, k, width):
    """Independent comparison via the lengths of cycles containing successive minima."""
    eulerian = eulerian_prefixes(n - 1, width)
    t = fmpz_poly([0, 1])
    rows = {}
    for size in range(k,n+1):
        row = eulerian[size-1]
        for length in range(k,size-k+1):
            row += comb(size-1,length-1)*t.mul_low(eulerian[length-1].mul_low(rows[size-length], width), width)
        rows[size]=row
    return rows[n]


def verify():
    sets = list(band_prefixes(80, 30, first_n=9))
    fixtures = [(3,9),(4,16),(9,26),(9,27),(9,28),(9,29),(9,36),(17,67),(20,80)]
    available = dict(sets)
    for k,n in fixtures:
        if available[k][n] != direct(n,k,30):
            raise ArithmeticError((k,n))
    print("Independent cycle recursion agrees on all fixtures.")


if __name__ == "__main__":
    import sys
    verify()
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    width = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    first = perf_counter()
    count = sum(len(rows) for _, rows in band_prefixes(limit, width))
    print(limit, width, count, round(perf_counter() - first, 2), "seconds")
