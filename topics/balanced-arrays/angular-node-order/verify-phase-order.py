#!/usr/bin/env python3
"""Certify phase ordering for all 2 <= d <= 128 and 1 <= r < d.

For F either H or B, put L_F = |F(w exp(i theta))|^2 and
K_F = Im[z F'(z) conjugate(F(z))], for theta = pi/d. Check that
every interior coefficient of 2 K_H L_B - K_B L_H is positive.
The constant and top-degree coefficients vanish identically.
All bounds and products use integer arithmetic.
"""

from argparse import ArgumentParser
from fractions import Fraction
from math import comb


SCALE = 1 << 192
TAYLOR_TERMS = 64


def ceildiv(top, bottom):
    return -(-top // bottom)


def arctan_bounds(denominator):
    """The two successive alternating partial sums enclose arctan(1/q)."""
    lower = sum(
        Fraction((-1) ** k, (2 * k + 1) * denominator ** (2 * k + 1))
        for k in range(TAYLOR_TERMS)
    )
    upper = lower + Fraction(
        1, (2 * TAYLOR_TERMS + 1) * denominator ** (2 * TAYLOR_TERMS + 1)
    )
    return lower, upper


def pi_bounds():
    """Machin's identity follows by taking tangents of 4 atan(1/5)-atan(1/239)."""
    low5, high5 = arctan_bounds(5)
    low239, high239 = arctan_bounds(239)
    lower = SCALE * (16 * low5 - 4 * high239)
    upper = SCALE * (16 * high5 - 4 * low239)
    return lower.numerator // lower.denominator, ceildiv(upper.numerator, upper.denominator)


def taylor_at_point(point, parity):
    """Enclose sine (parity 1) or cosine (parity 0) at point/SCALE."""
    square = point * point
    lo = hi = SCALE if parity == 0 else point
    sum_lo = sum_hi = 0
    for k in range(TAYLOR_TERMS):
        if k % 2 == 0:
            sum_lo += lo
            sum_hi += hi
        else:
            sum_lo -= hi
            sum_hi -= lo
        power = 2 * k + parity
        divisor = SCALE * SCALE * (power + 1) * (power + 2)
        lo = (lo * square) // divisor
        hi = ceildiv(hi * square, divisor)
    # The remaining terms have decreasing absolute values. The first
    # omitted term is positive because TAYLOR_TERMS is even.
    return sum_lo, sum_hi + hi


def angle_bounds(dimension, bounds):
    """Entries are outward-rounded bounds scaled by SCALE."""
    pi_lo, pi_hi = bounds
    sine = [(0, 0)] * dimension
    cosine = [(SCALE, SCALE)] * dimension
    for j in range(1, (dimension + 1) // 2):
        point = j * pi_lo // dimension
        error = ceildiv(j * pi_hi, dimension) - point
        s_lo, s_hi = taylor_at_point(point, 1)
        c_lo, c_hi = taylor_at_point(point, 0)
        # Both sine and cosine are 1-Lipschitz on the real line.
        sine[j] = sine[dimension - j] = (s_lo - error, s_hi + error)
        cosine[j] = (c_lo - error, c_hi + error)
        cosine[dimension - j] = (-c_hi - error, -c_lo + error)
    if dimension % 2 == 0:
        sine[dimension // 2] = (SCALE, SCALE)
        cosine[dimension // 2] = (0, 0)
    return sine, cosine


class AngularCoefficients:
    def __init__(self):
        self.coefficients = []
        self.k_lo = []
        self.k_hi = []
        self.l_lo = []
        self.l_hi = []

    def append(self, coefficient, sine, cosine):
        degree = len(self.coefficients)
        added = [0] if degree == 0 else [0, 0]
        self.k_lo.extend(added)
        self.k_hi.extend(added)
        self.l_lo.extend(added)
        self.l_hi.extend(added)
        for i, old in enumerate(self.coefficients):
            product = coefficient * old
            gap = degree - i
            index = degree + i
            sin_low, sin_high = sine[gap]
            cos_low, cos_high = cosine[gap]
            self.k_lo[index] += gap * product * sin_low
            self.k_hi[index] += gap * product * sin_high
            self.l_lo[index] += 2 * product * cos_low
            self.l_hi[index] += 2 * product * cos_high
        self.l_lo[2 * degree] = SCALE * coefficient * coefficient
        self.l_hi[2 * degree] = SCALE * coefficient * coefficient
        self.coefficients.append(coefficient)


def nonnegative_convolution(left, right):
    """Integer convolution via radix packing; the width rules out carries."""
    length = len(left) + len(right) - 1
    bits = max(left).bit_length() + max(right).bit_length()
    bits += min(len(left), len(right)).bit_length()
    width = max(1, ceildiv(bits, 8))

    def packed(values):
        return int.from_bytes(b"".join(value.to_bytes(width, "little") for value in values), "little")

    data = (packed(left) * packed(right)).to_bytes(width * length, "little")
    return [
        int.from_bytes(data[j : j + width], "little")
        for j in range(0, len(data), width)
    ]


def verify(max_dimension):
    pi = pi_bounds()
    caps = checked = exterior_zeros = 0
    for d in range(2, max_dimension + 1):
        sine, cosine = angle_bounds(d, pi)
        h = AngularCoefficients()
        b = AngularCoefficients()
        h.append(1, sine, cosine)
        for r in range(1, d):
            h.append(comb(d, r), sine, cosine)
            b.append(comb(d - 2, r - 1), sine, cosine)
            for values in (h.k_lo, b.l_lo, b.k_hi, h.l_hi):
                if min(values) < 0:
                    raise ArithmeticError(f"Nonnegative convolution input failed at {(d, r)}.")
            lhs = nonnegative_convolution(h.k_lo, b.l_lo)
            rhs = nonnegative_convolution(b.k_hi, h.l_hi)
            if lhs[0] != 0 or rhs[0] != 0 or lhs[-1] != 0 or rhs[-1] != 0:
                raise ArithmeticError(f"Structural endpoint check failed at {(d, r)}.")
            for k in range(1, len(lhs) - 1):
                if 2 * lhs[k] <= rhs[k]:
                    raise ArithmeticError(f"Coefficient sign not certified at {(d, r, k)}.")
            caps += 1
            exterior_zeros += 2
            checked += len(lhs) - 2
    print(f"d=2..{max_dimension}: {caps} caps, {checked} strictly positive coefficients, "
          f"{exterior_zeros} structural endpoint zeros; scale 2^192.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-d", type=int, default=128)
    arguments = parser.parse_args()
    if arguments.max_d < 2:
        parser.error("--max-d must be at least two")
    verify(arguments.max_d)
