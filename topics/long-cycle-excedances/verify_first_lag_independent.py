"""Reconstruct the first two-cycle boundary by finite differences and rational evaluation."""
from functools import lru_cache
from gzip import open as gzip_open
import json
from math import comb
from pathlib import Path

from flint import fmpq, fmpz_poly


@lru_cache(maxsize=3)
def eulerian(m):
    # The coefficient of t^j in (1-t)^(m+1) * sum_(h>=0) (h+1)^m t^h.
    powers = fmpz_poly([(h + 1) ** m for h in range(m)])
    return (fmpz_poly([1, -1]) ** (m + 1) * powers).truncate(m)


def nonzero_sign(value, expected):
    if expected * value <= 0:
        raise ArithmeticError("Incorrect sign in the boundary certificate")


def verify():
    archive = Path(__file__).with_name("first-lag-prefix.jsonl.gz")
    endpoints = central = 0
    with gzip_open(archive, "rt") as data:
        for k in range(3, 201):
            record = json.loads(next(data))
            if record["k"] != k or len(record["brackets"]) != k - 2:
                raise ArithmeticError(f"Wrong number of brackets at {k}")
            old, new, short = (eulerian(m) for m in (2*k-2, 2*k-1, k-1))
            scale = comb(2*k-1, k-1)
            if old(-1) != 0:
                raise ArithmeticError("Missing central root")
            for pencil in (1, -1):
                nonzero_sign(new(-1) - pencil * scale * short(-1)**2, (-1)**(k-1))
            central += 1
            prev = fmpq(0)
            for rank, pair in enumerate(record["brackets"], start=1):
                points = [fmpq(a, 2**b) for a, b in pair]
                lo, hi = points
                if not prev < lo < hi < 1:
                    raise ArithmeticError("Invalid rational bracket order")
                prev = hi
                sign = (-1)**rank
                for side, point in enumerate(points):
                    t = -point
                    nonzero_sign(old(t), sign if side else -sign)
                    base = new(t)
                    lag = scale * t * short(t)**2
                    nonzero_sign(base + lag, sign)
                    nonzero_sign(base - lag, sign)
                    endpoints += 1
        if data.read(1):
            raise ArithmeticError("Unexpected extra records")
    if (endpoints, central) != (39402, 198):
        raise ArithmeticError("Incomplete boundary replay")
    print(f"Checked three rational signs at each of {endpoints} endpoints and {central} central roots.")


if __name__ == "__main__":
    verify()
