"""Replay the finite nonprincipal first-moment bound with rational arithmetic."""

from fractions import Fraction
from functools import lru_cache
from math import ceil, isqrt
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
PAIRED = runpy.run_path(str(HERE.parent / "paired-residues" / "check.py"))
BIN_SCALE = 2**56
MOMENT_SCALE = 2**64
SLABS = (4, 6, 10, 16, 22, 28, 34, 40, 44, 48)


@lru_cache(maxsize=None)
def first_moment_upper(shape):
    """The two signed tails begin after the odd index 63."""
    assert 3 * shape * 63**2 >= 1
    head = 0
    for pole in range(3, 64, 2):
        denominator = (1 + shape * (pole**2 - 1))**96
        head += 2 * pole * ceil(MOMENT_SCALE / denominator)
    boundary = 1 + shape * (63**2 - 1)
    tail = ceil(MOMENT_SCALE / (190 * shape * boundary**95))
    return Fraction(head + tail, MOMENT_SCALE)


def nonprincipal_bound(lower, upper, product_counts):
    assert len(product_counts) == 241
    cost = Fraction(0)
    for b in range(5 * (upper - 1) + 1):
        fraction = max(Fraction(1, upper), 1 - Fraction(b, 4 * lower))
        shape = fraction / 160
        weight = Fraction(4, 7) if b + 8 <= 4 * lower else Fraction(1)
        cost += weight * first_moment_upper(shape) * Fraction(product_counts[b], BIN_SCALE)
    return cost


def main():
    reviewed = {
        (row[0], row[1]): row[5]
        for line in (HERE / "carrier-output.txt").read_text().splitlines()
        if (row := list(map(int, line.split())))
    }
    for lower, upper in zip(SLABS, SLABS[1:]):
        cutoff = 10000 // upper
        radius = Fraction(isqrt(192000) // upper, 4)
        counts, _ = PAIRED["coefficients"](cutoff, lower, upper, radius, 240)
        assert counts[0] == BIN_SCALE
        cost = nonprincipal_bound(lower, upper, counts)
        ceiling = ceil(10**6 * cost)
        assert ceiling <= reviewed[lower, upper]
        print(lower, upper, "maximum bin", 5 * (upper - 1), "upper millionths", ceiling)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    main()
