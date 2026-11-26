"""Regenerate and verify shifted rays of labeled capped arrays by exact arithmetic."""
import argparse
from collections import Counter, defaultdict
from functools import cache
import gzip
from itertools import combinations
import json
from math import factorial, prod
from pathlib import Path
import sys

from flint import fmpz_poly

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "shared/python"))
from roots import interlaces, root_report

ARCHIVE = HERE / "shifted-rays.jsonl.gz"
LIMITS = {(r, d): 8 for d in range(2, 6) for r in range(1, d+1)}
LIMITS.update({(2, 4): 20, (2, 5): 16, (3, 5): 16, (2, 6): 12, (3, 6): 12, (4, 6): 12})


@cache
def sturm(coefficients):
    return root_report(coefficients)


def through_wronskian(old, new):
    """Check old' * new - old * new' >= 0 on the real line."""
    old, new = fmpz_poly(old), fmpz_poly(new)
    w = old.derivative() * new - old * new.derivative()
    if not w:
        return True
    if w.degree() % 2 or w.leading_coefficient() < 0:
        return False
    _, factors = w.factor_squarefree()
    return all(multiplicity % 2 == 0 or sturm(tuple(factor))["distinct_real_roots"] == 0
               for factor, multiplicity in factors)


def row_supports(r, d):
    return [s for size in range(r+1) for s in combinations(range(d), size)]


def extend(margins, support):
    result = list(margins)
    for j in support:
        result[j] += 1
    return tuple(result)


def labeled_step(layer, supports):
    result = defaultdict(int)
    for margins, total in layer.items():
        for support in supports:
            result[extend(margins, support)] += total
    return result


def rays_for_shape(nmax, r, d):
    supports = row_supports(r, d)
    layers = {(0,)*d: 1}
    labeled = layers
    for n in range(nmax+1):
        profiles = defaultdict(dict)
        for u, total in layers.items():
            orbit = factorial(d) // prod(factorial(m) for m in Counter(u).values())
            a, rem = divmod(total, orbit)
            if rem:
                raise ArithmeticError((n, r, d, u))
            if n <= 4 and labeled[u] != a:
                raise ArithmeticError(("labeled check", n, r, d, u))
            k = u[0]
            profiles[tuple(i-k for i in u)][k] = a
        if n <= 4 and {tuple(sorted(u)) for u in labeled} != set(layers):
            raise ArithmeticError(("labeled support check", n, r, d))
        rays = {}
        for w, by_quota in profiles.items():
            if set(by_quota) != set(range(len(by_quota))):
                raise ArithmeticError(("ray support", n, r, d, w))
            rays[w] = [by_quota[i] for i in range(len(by_quota))]
        for w, f in sorted(rays.items()):
            report = sturm(tuple(f))
            edges = []
            for a in range(d):
                if a and w[a] == w[a-1]:
                    continue
                v = sorted(extend(w, (a,)))
                shift = v[0]
                v = tuple(j-shift for j in v)
                if v not in rays:
                    continue
                old, new = [0]*shift + f, rays[v]
                edges.append([a, interlaces(new, old), through_wronskian(old, new)])
            yield dict(n=n, r=r, d=d, offset=list(w), coefficients=f,
                       sturm=report, coordinate_edges=edges)
        if n == nmax:
            break
        next_layer = defaultdict(int)
        for u, total in layers.items():
            for support in supports:
                next_layer[tuple(sorted(extend(u, support)))] += total
        layers = next_layer
        if n < 4:
            labeled = labeled_step(labeled, supports)
    sturm.cache_clear()


def run(stream, write):
    counts = Counter()
    for (r, d), nmax in sorted(LIMITS.items(), key=lambda p: p[0][::-1]):
        for row in rays_for_shape(nmax, r, d):
            if write:
                stream.write(json.dumps(row, separators=(",", ":")) + "\n")
            else:
                line = stream.readline()
                if not line or json.loads(line) != row:
                    raise ArithmeticError(("archive difference", row))
            if not row["sturm"]["real_rooted"] or any(not (a and b) for _, a, b in row["coordinate_edges"]):
                raise ArithmeticError(("failed root or orientation check", row))
            counts["rays"] += 1
            counts["edges"] += len(row["coordinate_edges"])
    if not write and stream.readline():
        raise ArithmeticError("trailing archive records")
    if counts != {"rays": 80100, "edges": 295350}:
        raise ArithmeticError(counts)
    print(dict(counts), "all exact checks passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-archive", action="store_true",
                        help="regenerate the archive instead of checking it")
    args = parser.parse_args()
    if args.write_archive:
        import io
        with ARCHIVE.open("wb") as raw:
            with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as gz:
                with io.TextIOWrapper(gz, encoding="utf-8") as stream:
                    run(stream, write=True)
    else:
        with gzip.open(ARCHIVE, "rt", encoding="utf-8") as stream:
            run(stream, write=False)


if __name__ == "__main__":
    main()
