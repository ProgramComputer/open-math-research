"""Exact coefficient reconstruction and sign certificates for U(2,4)."""
from argparse import ArgumentParser
from functools import cache
import gzip
import io
import json
from math import atan2, comb, pi, sqrt
from pathlib import Path
from time import monotonic

from flint import arb, arb_poly, ctx, fmpz, fmpz_poly


DENOMINATOR = 1 << 32
SQRT2 = sqrt(2)
BLOCK = 64


def factorial_table(last):
    table = [fmpz(1)]
    for i in range(1, last+1):
        table.append(table[-1]*i)
    return table


def scaled_exponential(length, factorials):
    """Integer coefficients of exp(x) through length, scaled by length!."""
    scale = factorials[length]
    return fmpz_poly([scale//factorials[j] for j in range(length+1)])


def matching_counts(k, factorials):
    """All matching sizes of K_{k,k,k,k}, by internal-edge inclusion-exclusion."""
    internal = fmpz_poly([
        factorials[k]//((factorials[k-2*j]*factorials[j]) << j)
        for j in range(k//2+1)
    ])
    forbidden = internal**4
    signed = fmpz_poly([
        (((-1)**a)*forbidden[a]*factorials[4*k-2*a]) << a
        for a in range(forbidden.degree()+1)
    ])
    product = signed*scaled_exponential(2*k, factorials)
    scale = factorials[2*k]
    counts = []
    for p in range(2*k+1):
        denominator = (scale*factorials[4*k-2*p]) << p
        value, remainder = divmod(product[p], denominator)
        if remainder or value < 0:
            raise ArithmeticError(f"invalid matching count at {k=}, {p=}")
        counts.append(value)
    return counts


@cache
def split_matchings(k):
    """Independent count by appending one color at a time, for small quotas."""
    counts = [1]
    for color in range(4):
        updated = [0]*((color+1)*k//2+1)
        for p, ways in enumerate(counts):
            free = color*k-2*p
            new_ways = 1
            for j in range(min(k,free)+1):
                updated[p+j] += ways*new_ways
                new_ways = new_ways*(free-j)*(k-j)//(j+1)
        counts = updated
    return counts


def coefficient_rows(last, first=0, crosscheck=24):
    """Rows of original a(n,k), indexed by n-first, with quota increasing."""
    factorials = factorial_table(2*last)
    rows = [[] for _ in range(last-first+1)]
    for k in range(last//2+1):
        counts = matching_counts(k, factorials)
        if k <= crosscheck and counts != split_matchings(k):
            raise ArithmeticError(f"independent matching count disagreement for {k=}")
        shift = 2*k
        degree = last-shift
        product = fmpz_poly(list(reversed(counts)))*scaled_exponential(degree, factorials)
        scale = factorials[degree]*factorials[k]**4
        for n in range(max(first,shift),last+1):
            value, remainder = divmod(product[n-shift]*factorials[n], scale)
            if remainder or value <= 0:
                raise ArithmeticError(f"invalid row coefficient at {n=}, {k=}")
            rows[n-first].append(value)
    return rows


def phase(n, t):
    shared = SQRT2*t
    theta = atan2(2*shared+6*t*t, 1+2*shared)
    numerator_angle = atan2(shared+4*t*t, shared)
    return (n+1.5)*theta-1.5*numerator_angle


def sample_numerators(n):
    """Approximate integer phase levels, then round coordinates to dyadics."""
    points = []
    lo = 0.0
    ceiling = float(max(1,n))
    for j in range(1,n//2):
        hi = ceiling
        target = j*pi
        if phase(n, hi) <= target:
            raise ArithmeticError(f"phase bracketing failed at {n=}, {j=}")
        for _ in range(46):
            mid = (lo+hi)/2
            if phase(n, mid) < target:
                lo = mid
            else:
                hi = mid
        points.append(round((lo+hi)*DENOMINATOR/2))
    if points and (points[0] <= 0 or any(a >= b for a,b in zip(points,points[1:]))):
        raise ArithmeticError(f"sample ordering failed at {n=}")
    return points


def integer_horner(coefficients, t_numerator):
    """Sign of P(-t^4) after multiplication by a positive denominator."""
    q_num = -fmpz(t_numerator)**4
    q_den = fmpz(DENOMINATOR)**4
    common = q_num.gcd(q_den)
    q_num //= common
    q_den //= common
    value = coefficients[-1]
    power = 1
    for coefficient in coefficients[-2::-1]:
        power *= q_den
        value = value*q_num+coefficient*power
    return (value > 0)-(value < 0)


def sign_certificate(n, coefficients, recorded_points=None):
    if len(coefficients) != n//2+1 or coefficients[0] != 1 or coefficients[-1] <= 0:
        raise ArithmeticError(f"degree or endpoint sign failed at {n=}")
    points = sample_numerators(n) if recorded_points is None else recorded_points
    if (len(points) != max(0,n//2-1) or any(t <= 0 for t in points)
            or any(a >= b for a,b in zip(points,points[1:]))):
        raise ValueError(f"invalid rational nodes for {n=}")
    ctx.prec = max(96, n//2+64)
    polynomial = arb_poly(coefficients)
    fallback = []
    for j, numerator in enumerate(points,1):
        point = -(arb(numerator)/DENOMINATOR)**4
        value = polynomial(point)
        sign = (value > 0)-(value < 0)
        if not sign:
            sign = integer_horner(coefficients, numerator)
            fallback.append(j)
        if sign != (-1)**j:
            raise ArithmeticError(f"sign alternation failed at {n=}, {j=}, {numerator=}, {sign=}")
    return {
        "n": n, "a": [int(coefficient) for coefficient in coefficients],
        "t_denominator": DENOMINATOR, "t_numerators": points,
        "arb_bits": ctx.prec, "integer_fallback": fallback,
    }


def generate(directory, first, last):
    started = monotonic()
    coefficients = coefficient_rows(last, first)
    print(f"Computed {len(coefficients)} coefficient rows in {monotonic()-started:.2f}s.", flush=True)
    directory.mkdir(parents=True, exist_ok=True)
    for begin in range(first,last+1,BLOCK):
        end = min(last,begin+BLOCK-1)
        target = directory / f"rows-{begin:04d}-{end:04d}.jsonl.gz"
        staging = target.with_suffix(".tmp")
        with staging.open("wb") as raw, gzip.GzipFile(fileobj=raw,mode="wb",mtime=0) as packed:
            with io.TextIOWrapper(packed) as out:
                for n in range(begin,end+1):
                    record = sign_certificate(n, coefficients[n-first])
                    out.write(json.dumps(record, separators=(",",":"))+"\n")
        staging.replace(target)
        print(f"Certified rows {begin}–{end} at {monotonic()-started:.2f}s.", flush=True)


def verify(directory, first, last, recompute):
    coefficients = coefficient_rows(last,first) if recompute else None
    expected = first
    node_count = 0
    fallbacks = 0
    for source in sorted(directory.glob("rows-*.jsonl.gz")):
        with gzip.open(source,"rt") as stream:
            for line in stream:
                record = json.loads(line)
                n = record["n"]
                if not first <= n <= last:
                    continue
                if n != expected or record["t_denominator"] != DENOMINATOR:
                    raise ValueError(f"unexpected archive row {n}, expected {expected}")
                row = [fmpz(coefficient) for coefficient in record["a"]]
                if coefficients is not None and row != coefficients[n-first]:
                    raise ValueError(f"coefficient mismatch at {n=}")
                certified = sign_certificate(n, row, record["t_numerators"])
                if certified != record:
                    raise ValueError(f"certificate replay mismatch for {n=}")
                expected += 1
                node_count += len(record["t_numerators"])
                fallbacks += len(record["integer_fallback"])
    if expected != last+1:
        raise ValueError(f"missing archive rows starting at n={expected}")
    print(f"Verified rows {first}–{last}, {node_count} dyadic signs, {fallbacks} exact fallback evaluations.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=Path(__file__).parent/"rows")
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--last", type=int, required=True)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--signs-only", action="store_true")
    args = parser.parse_args()
    if not 0 <= args.first <= args.last:
        parser.error("require 0 <= --first <= --last")
    if args.verify:
        verify(args.directory,args.first,args.last,recompute=not args.signs_only)
    else:
        generate(args.directory,args.first,args.last)
