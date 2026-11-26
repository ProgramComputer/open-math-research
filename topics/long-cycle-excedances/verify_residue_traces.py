"""Exact sums of squared insertion ratios over reciprocal orbits of old roots."""
import argparse
from functools import cache
import gzip
import json
from math import comb
from pathlib import Path
from flint import fmpq, fmpq_poly as Poly

X = Poly([0, 1])
TOPIC = Path(__file__).resolve().parent
ARCHIVE = TOPIC / "insertion-lag.jsonl.gz"


@cache
def eulerian(n):
    a = Poly([1])
    for j in range(1, n + 1):
        a = (1 + (j - 1)*X)*a + X*(1 - X)*a.derivative()
    return a


def reciprocal_basis(p, degree):
    """Write p(t)=(1+t)^degree g(t/(1+t)^2) by triangular elimination."""
    coeff = [p[j] for j in range(degree+1)]
    gamma = []
    for i in range(degree//2+1):
        lead = coeff[i]
        gamma.append(lead)
        for j in range(degree-2*i+1):
            coeff[i+j] -= lead * comb(degree-2*i, j)
    if any(coeff):
        raise ValueError("Input violates reciprocity")
    return Poly(gamma)


def trace_square(p, d, lag):
    if p.degree() == 0:
        return 0
    gcd, inv, _ = d.xgcd(p)
    if gcd != 1:
        raise ValueError("Trace requires simple roots, none at poles")
    b = (inv * lag) % p
    return ((p.derivative() * (b*b % p)) % p)[p.degree()-1] / p.leading_coefficient()


def verify(old, lag, compare):
    m = old.degree()
    d = X*(1-X)*old.derivative()
    center = lag(-1)/d(-1) if m % 2 else 0
    g = reciprocal_basis(old, m)
    h = reciprocal_basis(lag, m+1)
    orbit_sum = trace_square(g, X*(1-4*X)*g.derivative(), h) + center**2
    if compare:
        direct = trace_square(old, d, lag)
        if direct + center**2 != 2*orbit_sum:
            raise ArithmeticError("Full trace disagrees with reciprocal-orbit trace")
    return orbit_sum


def records():
    with gzip.open(ARCHIVE, "rt") as source:
        rows = {(r["n"], r["k"]): Poly(r["coefficients"]) for r in map(json.loads, source)}
    for n in range(5, 46):
        for k in range(3, (n + 1)//2 + 1):
            p = rows[n, k]//X
            lag = comb(n, k-1) * eulerian(k-1) * rows[n+1-k, k]
            value = verify(p, lag, n <= 17)
            yield {"n": n, "k": k, "sum": str(value), "full_trace_checked": n <= 17}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--write", action="store_true", help="create a new trace archive")
    cli.add_argument("--archive", type=Path, default=TOPIC / "squared-traces.jsonl.gz")
    args = cli.parse_args()
    count = 0
    best = None
    maximizers = []
    with args.archive.open("xb" if args.write else "rb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb" if args.write else "rb",
                           **({"mtime": 0} if args.write else {})) as data:
            for record in records():
                if args.write:
                    data.write((json.dumps(record, separators=(",",":")) + "\n").encode("ascii"))
                elif json.loads(data.readline()) != record:
                    raise ArithmeticError(f"Trace mismatch at {record['n'],record['k']}")
                count += 1
                value = fmpq(record["sum"])
                pair = (record["n"], record["k"])
                if best is None or value > best:
                    best, maximizers = value, [pair]
                elif value == best:
                    maximizers.append(pair)
            if not args.write and data.read(1):
                raise ArithmeticError("Unexpected extra records")
    if (count, best, maximizers) != (441, fmpq(25, 36), [(5, 3)]):
        raise ArithmeticError("Unexpected range or extremum")
    print(f"Verified {count} nonzero lags. Unique maximum {best} at {maximizers[0]}.")


if __name__ == "__main__":
    main()
