"""Check independent recurrences, the tail constants, and selected certified residues."""

import argparse
import gzip
import json
import sys
from pathlib import Path
from fractions import Fraction
from math import comb, factorial

from flint import acb, arb, ctx, fmpq, fmpz_poly


def first_block_rows(limit):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([1])]
    for n in range(1, limit+1):
        large = sum((comb(n, s)*rows[n-s] for s in range(2, n+1)), fmpz_poly([]))
        rows.append(n*rows[n-1] + t*large)
    return rows


def delayed_rows(limit):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([1]), fmpz_poly([1])]
    for n in range(1, limit):
        current, previous = rows[n], rows[n-1]
        following = ((n+1)*current + 2*t*current.derivative()
                     + n*t*(previous + (t-1)*previous.derivative()))
        rows.append(following)
    return rows


def to_ball(value):
    return arb(fmpq(value.numerator, value.denominator))


def phase_function(theta):
    return theta*theta.cos()/theta.sin() - (theta/theta.sin()).log()


def principal_angle(logp):
    """Use interval signs and the proved monotonicity of phase_function."""
    left, right = Fraction(0), Fraction(1)
    if not phase_function(arb(1)) < logp < arb(1):
        raise ArithmeticError("The angle is outside the principal branch")
    for _ in range(190):
        middle = (left+right)/2
        test = phase_function(to_ball(middle))-logp
        if test > 0:
            left = middle
        elif test < 0:
            right = middle
        else:
            raise ArithmeticError("Increase Arb precision for the angle bisection")
    return arb(to_ball((left+right)/2), to_ball((right-left)/2))


def check_residue(rows, q):
    """Compare the exact coefficient with the certified principal residues."""
    v = 1 / (1+q)
    a = 1-2*v
    logp = to_ball(a) - to_ball(1-v).log()
    theta = principal_angle(logp)
    u = acb(theta*theta.cos()/theta.sin(), theta)
    z = u-to_ball(a)
    if not z.real > 0 or not abs(z) < arb(5).sqrt():
        raise ArithmeticError(f"Unexpected principal pole at q={q}")
    for n in (2, 3, 8, 17, 41, 104):
        N = n+1
        actual = arb(rows[n](-fmpq(q.numerator, q.denominator))/factorial(n))
        principal = -2*(1/((u-1)*z**N)).real / to_ball(1+q)
        normalizer = 2 / (to_ball(1+q)*abs(u-1)*abs(z)**N)
        normalized_error = abs(actual-principal)/normalizer
        if not normalized_error < theta*to_ball(Fraction(3, 8)**(N+1)):
            raise ArithmeticError(f"Residue bound failed at n={n}, q={q}")


def verify_archive(rows, write):
    shared = Path(__file__).resolve().parents[3] / "shared" / "python"
    sys.path.insert(0, str(shared))
    from roots import interlaces, root_report

    cases = []
    for n, row in enumerate(rows):
        a = [int(c) for c in row]
        report = root_report(a)
        strict = None
        if n:
            strict = rows[n-1].gcd(row).degree() == 0 and interlaces(rows[n-1], row)
        if report["distinct_real_roots"] != n//2 or strict is False:
            raise ArithmeticError(f"Sturm or interlacing failure at row {n}")
        cases.append({"n": n, "coefficients": a, "sturm": report,
                      "strict_previous_interlacing": strict})
    path = Path(__file__).resolve().parents[1] / "results" / "threshold-two.json.gz"
    if write:
        path.write_bytes(gzip.compress(json.dumps(cases, separators=(',', ':')).encode(),
                                       compresslevel=9, mtime=0))
    elif json.loads(gzip.decompress(path.read_bytes())) != cases:
        raise ValueError("The stored coefficients or exact checks differ")
    return len(cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the local archive")
    args = parser.parse_args()
    limit = 104
    rows = first_block_rows(limit)
    if rows != delayed_rows(limit):
        raise ArithmeticError("The two recurrences disagree")
    if any(p[0] != factorial(n) or p.degree() != n//2 for n, p in enumerate(rows)):
        raise ArithmeticError("Unexpected degree or constant term")
    gap = Fraction(3, 8)
    if not Fraction(9, 4)*gap**4*(1+gap) < Fraction(1, 4):
        raise ArithmeticError("The consecutive-row rational error bound failed")
    ctx.prec = 410
    if not arb.pi() > 3 or not arb(2).log() > arb(1)/2:
        raise ArithmeticError("The elementary bounds on pi and log(2) failed")
    for q in (Fraction(1, 3), Fraction(1), Fraction(16), Fraction(256)):
        check_residue(rows, q)
    nrows = verify_archive(rows, args.write)
    print(f"Two recurrences, {nrows} Sturm counts and {nrows-1} strict interlacings verified.")
    print("Certified 24 principal-residue comparisons and the rational interlacing margin.")


if __name__ == "__main__":
    main()
