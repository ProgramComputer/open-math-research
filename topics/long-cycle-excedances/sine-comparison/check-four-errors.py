"""Join all four rational cost bounds against the verified principal lower bounds."""

from fractions import Fraction
from math import ceil, floor, isqrt
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
ATOM = runpy.run_path(str(HERE / "check-cutoff-jump.py"))
REGULAR = ATOM["REGULAR"]
COMMON = REGULAR["COMMON"]
PAIRED = COMMON["PAIRED"]
LOWER_MARGIN = Fraction(325873, 10**6)


def main():
    for lower, upper in zip(COMMON["SLABS"], COMMON["SLABS"][1:]):
        radius = Fraction(isqrt(192000) // upper, 4)
        counts, _ = PAIRED["coefficients"](10000 // upper, lower, upper, radius, 240)
        assert len(counts) == 241 and counts[0] == COMMON["BIN_SCALE"]
        principal = Fraction(1, 10000)
        for b, count in enumerate(counts):
            principal += 2 * PAIRED["eps"](lower - Fraction(b, 4)) * Fraction(count, COMMON["BIN_SCALE"])
        nonprincipal = COMMON["nonprincipal_bound"](lower, upper, counts)
        regular = REGULAR["regular_bound"](lower, upper, radius, counts)
        atom = ATOM["single_cost"](lower, upper, radius) + ATOM["multiple_cost"](lower, upper, radius, counts)
        carrier = Fraction(54, 55) if upper <= 10 else Fraction(6000, 12243)
        margin = carrier - principal - nonprincipal - regular - atom
        ceilings = tuple(ceil(10**6 * c) for c in (principal, nonprincipal, regular, atom))
        coarse_margin = carrier - Fraction(sum(ceilings), 10**6)
        assert margin >= coarse_margin > LOWER_MARGIN
        print(lower, upper, "error ceilings", *ceilings, "rounded margin floor", floor(10**6 * coarse_margin),
              "unrounded margin floor", floor(10**6 * margin))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    main()
