"""Recheck once-source-normalized polynomials from pinned Git archives."""
import gzip
import json
from fractions import Fraction
from math import comb, gcd, lcm
from subprocess import PIPE, Popen

COMMIT = "1740556cba01ba9d32731d31cc9789e657c19126"
ARCHIVES = ("corank-one.jsonl.gz", "column-extension-cap-two.jsonl.gz", "source_range.jsonl")


def records(name):
    path = "topics/balanced-arrays/results/" + name
    with Popen(["git", "show", COMMIT + ":" + path], stdout=PIPE) as git:
        stream = gzip.GzipFile(fileobj=git.stdout) if name.endswith(".gz") else git.stdout
        with stream as archive:
            for line in archive:
                yield json.loads(line)
        if git.wait():
            raise RuntimeError("cannot read pinned archive " + name)


def primitive(poly):
    denominator = lcm(*(entry.denominator for entry in poly))
    integers = [int(entry * denominator) for entry in poly]
    divisor = gcd(*integers)
    return [entry // divisor for entry in integers]


def remainder(poly, divisor):
    work = list(map(Fraction, poly))
    while work and len(work) >= len(divisor):
        multiplier = work[-1] / divisor[-1]
        shift = len(work) - len(divisor)
        for j, entry in enumerate(divisor):
            work[shift + j] -= multiplier * entry
        while work and work[-1] == 0:
            work.pop()
    return work


def variations(signs):
    return sum(a != b for a, b in zip(signs, signs[1:]))


def real_rooted(poly):
    if len(poly) == 1:
        return True
    chain = [primitive(poly), primitive([k * poly[k] for k in range(1, len(poly))])]
    while error := remainder(*chain[-2:]):
        chain.append(primitive([-entry for entry in error]))
    right = [entry[-1] > 0 for entry in chain]
    left = [sign if len(entry) % 2 else not sign for entry, sign in zip(chain, right)]
    distinct_degree = len(poly) - len(chain[-1])
    return variations(left) - variations(right) == distinct_degree


def main():
    all_tested = {}
    for name in ARCHIVES:
        tested = {}
        for row in records(name):
            n, r, d = (row[k] for k in ("n", "r", "d"))
            shapes = [(d, row["coefficients"])] if "coefficients" in row else [
                (d, row["left"]), (d + 1, row["right"])]
            for dimension, coefficients in shapes:
                if dimension < 2:
                    continue
                key = n, r, dimension
                if key in tested:
                    assert coefficients == tested[key]
                    continue
                tested[key] = coefficients
                normalized = [Fraction(value, comb(n, k)) for k, value in enumerate(coefficients)]
                if not real_rooted(normalized):
                    raise ArithmeticError((name, n, r, dimension))
        assert all(coefficients == all_tested.get(key, coefficients)
                   for key, coefficients in tested.items())
        all_tested.update(tested)
        print(name, len(tested))
    print("Combined distinct cases", len(all_tested))


if __name__ == "__main__":
    main()
