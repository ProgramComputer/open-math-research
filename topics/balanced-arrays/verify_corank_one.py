"""Independent column-intersection counts, determinant identity, and strict interlacing."""

import argparse
import gzip
import json
from math import comb, factorial
from pathlib import Path

from flint import fmpq_poly, fmpz_mat, fmpz_poly


def column_counts(n, max_d):
    # With no columns yet their intersection is the full row set.
    result = [[0] * (n + 1) for _ in range(max_d + 1)]
    for k in range(n + 1):
        counts = {n: 1}
        moves = {
            s: [(j, comb(s, j) * comb(n - s, k - j))
                for j in range(max(0, k + s - n), min(s, k) + 1)]
            for s in range(n + 1)
        }
        for d in range(1, max_d + 1):
            next_counts = {}
            for s, count in counts.items():
                for j, ways in moves[s]:
                    next_counts[j] = next_counts.get(j, 0) + count * ways
            counts = next_counts
            result[d][k] = counts.get(0, 0)
    return result


def direct_determinants(n, d, row):
    if n == 0:
        if row != [1]:
            raise ValueError("Empty array count differs from one")
        return [1]
    m = fmpz_mat(n, n)
    u = fmpz_mat(n, n)
    for i in range(n):
        m[i, i] = i + 1
        if i:
            m[i, i - 1] = 1
            u[i - 1, i] = 1
    a = m ** (d - 1)
    # Both sides have degree <= n. These n+1 integer specializations certify equality.
    weighted = fmpz_poly([entry * factorial(n - k) ** d for k, entry in enumerate(row)])
    evaluations = []
    for q in range(n + 1):
        det = int((a - q * u).det())
        if factorial(n) * det != weighted(q):
            raise ValueError(f"Determinant mismatch at {(n, d, q)}")
        evaluations.append(det)
    return evaluations


def primitive(poly):
    integer_poly = poly.numer()
    return fmpq_poly(integer_poly // integer_poly.content())


def positive_chain(bigger, smaller):
    """The second polynomial has one fewer degree and lies between roots of the first."""
    p, q = fmpq_poly(bigger), fmpq_poly(smaller)
    degrees = [p.degree(), q.degree()]
    if p.degree() != q.degree() + 1 or p.leading_coefficient() <= 0 or q.leading_coefficient() <= 0:
        raise ValueError("Incorrect input degrees or orientation")
    while q.degree() > 0:
        r = -(p % q)
        if r.degree() != q.degree() - 1 or r.leading_coefficient() <= 0:
            raise ValueError("Strict interlacing chain failed")
        p, q = q, primitive(r)
        degrees.append(q.degree())
    return degrees


def records():
    prior = {}
    for n in range(25):
        rows = column_counts(n, 12)
        for d in range(2, 13):
            row = rows[d]
            p = fmpz_poly(row)
            if p.degree() != (n * (d - 1)) // d or p[0] != 1:
                raise ValueError("Incorrect degree or constant coefficient")
            det = direct_determinants(n, d, row)
            roots = positive_chain(p, p.derivative()) if p.degree() else []
            pair = []
            if d in prior and prior[d].degree():
                old = prior[d]
                if p.degree() == old.degree() + 1:
                    pair = positive_chain(p, old)
                else:
                    # Old roots precede the new roots in increasing (signed) order.
                    # The roots of x*old alternate with the new, ending with x=0.
                    pair = positive_chain(fmpz_poly([0, 1]) * old, p)
            yield dict(n=n, r=d - 1, d=d, coefficients=row[:p.degree() + 1],
                       determinants_at_0_through_n=det, sturm_degrees=roots,
                       consecutive_chain_degrees=pair)
            prior[d] = p


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="create a new archive")
    parser.add_argument("--archive", type=Path,
                        default=Path(__file__).with_name("results") / "corank-one.jsonl.gz")
    args = parser.parse_args()
    rows = samples = pairs = 0
    with args.archive.open("xb" if args.write else "rb") as stream:
        with gzip.GzipFile(filename="", mode="wb" if args.write else "rb", fileobj=stream,
                           **({"mtime": 0} if args.write else {})) as data:
            for record in records():
                if args.write:
                    data.write((json.dumps(record, separators=(",", ":")) + "\n").encode())
                elif json.loads(data.readline()) != record:
                    raise ValueError(f'Archive mismatch at {(record["n"], record["d"])}')
                rows += 1
                samples += len(record["determinants_at_0_through_n"])
                pairs += bool(record["consecutive_chain_degrees"])
            if not args.write and data.read(1):
                raise ValueError("Unexpected extra records")
    print(f"{rows} rows, {samples} integer determinant values, {pairs} consecutive nonconstant pairs")


if __name__ == "__main__":
    main()
