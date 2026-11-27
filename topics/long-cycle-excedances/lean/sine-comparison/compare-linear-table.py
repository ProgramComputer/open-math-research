#!/usr/bin/env python3
"""Compare the executable Lean table to the existing exact production formula."""

import argparse
import ast
from fractions import Fraction
from math import isqrt
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[2]
SLAB_ENDS = (6, 10, 16, 22, 28, 34, 40, 44, 48)


def main(evaluated):
    reference = runpy.run_path(str(ROOT / "degree-blocks" / "verify_degree_blocks.py"))
    rows = {}
    for line in evaluated.read_text().splitlines():
        slab, values = line.split(" ", 1)
        if int(slab) in rows:
            raise ValueError(f"duplicate slab {slab}")
        rows[int(slab)] = ast.literal_eval(values)
    if tuple(rows) != SLAB_ENDS:
        raise ValueError(f"unexpected slab order: {tuple(rows)}")
    for x in SLAB_ENDS:
        k = 10000 // x
        angle = Fraction(isqrt(192000) // x, 4)
        expected = [0] * 241
        for i, lower, mass in reference["degree_masses"](k, 60):
            shape = (lower - Fraction(1, k)) * Fraction(6, 5) / (192 * x)
            expected[i] = reference["up"](mass * reference["stars"](shape)[0] / angle)
        if rows[x] != expected:
            raise ArithmeticError(f"Lean and Python tables differ for upper aspect {x}")
        print(f"Aspect endpoint {x}: all 241 entries match", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evaluated", type=Path)
    main(parser.parse_args().evaluated)
