"""Check the regular numerator error for the nine angular aspect intervals."""

from fractions import Fraction
from functools import lru_cache
from math import ceil, factorial, isqrt
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
COMMON = runpy.run_path(str(HERE / "check-nonprincipal.py"))
BIN_SCALE = COMMON["BIN_SCALE"]
MOMENT_SCALE = COMMON["MOMENT_SCALE"]


@lru_cache(maxsize=None)
def zeroth_moment_upper(shape):
    """The two signed tails begin after absolute odd index 63."""
    assert 3 * shape * 63**2 >= 1
    head = 0
    for pole in range(1, 64, 2):
        base = 1 + shape * (pole**2 - 1)
        head += 2 * ceil(MOMENT_SCALE / base**96)
    boundary = 1 + shape * (63**2 - 1)
    tail = ceil(MOMENT_SCALE / (190 * shape * 63 * boundary**95))
    return Fraction(head + tail, MOMENT_SCALE)


def regular_bound(lower, upper, radius, counts):
    assert len(counts) == 241 and counts[0] == BIN_SCALE
    cost = Fraction(0)
    for b in range(5 * (upper - 1) + 1):
        block = max(0, lower - (b + 3) // 4)
        weight = Fraction(1, 2 * factorial(block)) if block >= 2 else Fraction(1)
        fraction = max(Fraction(1, upper), 1 - Fraction(b, 4 * lower))
        cost += Fraction(counts[b], BIN_SCALE) * weight * zeroth_moment_upper(fraction / 160) / radius
    return cost


def main():
    for line in (HERE / "carrier-output.txt").read_text().splitlines():
        lower, upper, _, _, _, _, previous, _, _ = map(int, line.split())
        radius = Fraction(isqrt(192000) // upper, 4)
        counts, _ = COMMON["PAIRED"]["coefficients"](10000 // upper, lower, upper, radius, 240)
        ceiling = ceil(10**6 * regular_bound(lower, upper, radius, counts))
        assert ceiling <= previous
        print(lower, upper, "regular upper millionths", ceiling, "previous", previous)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    main()
