"""Decide a fixed skew shape for all unweighted uniform-cap balanced arrays.

Dependencies are Python 3.10+ and python-flint 0.9.0. The first positional
argument is a comma-separated partition. Pass the inner shape with --inner.
"""
import argparse
from fractions import Fraction
from math import ceil, comb
from pathlib import Path
import runpy

engine = runpy.run_path(str(Path(__file__).with_name('factorial-schur-test.py')))


def read_partition(arg):
    try:
        parts = tuple(map(int, arg.split(','))) if arg else ()
    except ValueError as error:
        raise argparse.ArgumentTypeError("enter comma-separated positive parts") from error
    if any(k < 1 for k in parts) or list(parts) != sorted(parts, reverse=True):
        raise argparse.ArgumentTypeError("parts must be positive and weakly decreasing")
    return parts


def negative_height(values):
    """Return a negative integer-height witness, or None. Height zero is allowed."""
    if all(a >= 0 for a in values):
        return None
    # Convert sum values[j] binom(n,j) to ordinary powers, over Q.
    power = [Fraction(0)] * len(values)
    basis = [Fraction(1)]
    for j, coefficient in enumerate(values):
        for i, t in enumerate(basis):
            power[i] += coefficient*t
        basis = [(a-j*b)/(j+1) for a,b in zip([Fraction(0)]+basis,basis+[Fraction(0)])]
    while len(power)>1 and not power[-1]:
        power.pop()
    if len(power)==1:
        return 0 if power[0]<0 else None
    beyond_roots = 2 + ceil(max(abs(a/power[-1]) for a in power[:-1]))
    if power[-1]<0:
        return beyond_roots
    for n in range(beyond_roots):
        if sum(a*comb(n,j) for j,a in enumerate(values[:n+1])) < 0:
            return n
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('outer',type=read_partition)
    parser.add_argument('--inner',type=read_partition,default=())
    args = parser.parse_args()
    outer, inner = args.outer, args.inner
    if len(inner)>len(outer) or any(b>a for a,b in zip(outer,inner)):
        parser.error("inner must be contained in outer")
    if outer == inner:
        print("The empty shape has determinant one at every parameter.")
        return
    weight = sum(outer)-sum(inner)
    cutoff = engine['cutoff'](outer,inner)
    print("All dimensions at least",cutoff,"satisfy the coefficientwise bound.")
    largest = max(map(max,engine['quota_matrix'](outer,inner)))
    checked = 0
    for d in range(1,cutoff):
        for r in range(1,d+1):
            counts=engine['all_counts'](d,r,largest,d*weight)
            vector=engine['coefficients'](outer,d,counts,inner)
            n=negative_height(vector)
            if n is not None:
                value=sum(v*comb(n,k) for k,v in enumerate(vector[:n+1]))
                print("Negative determinant", value, "at (n,r,d)",(n,r,d))
                return
            checked+=1
    print("Nonnegative for every n,r,d;",checked,"residual dimension/cap pairs checked.")


if __name__=='__main__':
    main()
