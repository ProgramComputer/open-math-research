#!/usr/bin/env python3
"""Independently certify the phase-order coefficients for dimensions 2..35.

Isolate cos(pi/d) as the largest root of U_(d-1) using exact bisection.
Evaluate cosine and sine divided by sin(pi/d) by Chebyshev recurrence.
Use signed endpoint arithmetic and ordinary, unpacked convolution.
"""

from math import comb


SCALE = 1 << 256


def floor_interval(numerator, denominator):
    return numerator * SCALE // denominator


def ceil_interval(numerator, denominator):
    return -((-numerator * SCALE) // denominator)


def scaled_U(degree, numerator, denominator):
    """Return denominator**degree times U_degree(numerator/denominator)."""
    previous, current = 0, 1
    for _ in range(degree):
        previous, current = current, 2 * numerator * current - denominator**2 * previous
    return current


def cos_base(dimension):
    if dimension == 2:
        return (0, 0)
    denominator = dimension**2
    lower, upper = denominator - 8, denominator
    assert scaled_U(dimension - 1, lower, denominator) < 0
    assert scaled_U(dimension - 1, upper, denominator) > 0
    for _ in range(256):
        middle = lower + upper
        lower, upper, denominator = 2 * lower, 2 * upper, 2 * denominator
        sign = scaled_U(dimension - 1, middle, denominator)
        if sign == 0:
            lower = upper = middle
            break
        if sign < 0:
            lower = middle
        else:
            upper = middle
    return floor_interval(lower, denominator), ceil_interval(upper, denominator)


def add(left, right):
    return left[0] + right[0], left[1] + right[1]


def subtract(left, right):
    return left[0] - right[1], left[1] - right[0]


def scale_interval(interval, scalar):
    return tuple(sorted((scalar * interval[0], scalar * interval[1])))


def product_endpoints(left, right):
    corners = tuple(x * y for x in left for y in right)
    return min(corners), max(corners)


def multiply_scaled(left, right):
    lo, hi = product_endpoints(left, right)
    return lo // SCALE, -(-hi // SCALE)


def angle_intervals(dimension):
    x = cos_base(dimension)
    double_x = scale_interval(x, 2)
    zero = (0, 0)
    one = (SCALE, SCALE)
    cosine = [one, x]
    sine_ratio = [zero, one]
    while len(cosine) < dimension:
        cosine.append(subtract(multiply_scaled(double_x, cosine[-1]), cosine[-2]))
        sine_ratio.append(subtract(multiply_scaled(double_x, sine_ratio[-1]), sine_ratio[-2]))
    return cosine, sine_ratio


def angular_coefficients(row, cosine, sine_ratio):
    """Use every ordered pair, with K divided by the common positive sine."""
    size = 2 * len(row) - 1
    k = [(0, 0)] * size
    l = [(0, 0)] * size
    for i, left in enumerate(row):
        for j, right in enumerate(row):
            gap = i - j
            product = left * right
            l[i + j] = add(l[i + j], scale_interval(cosine[abs(gap)], product))
            sign = -1 if gap < 0 else 1
            k[i + j] = add(k[i + j], scale_interval(sine_ratio[abs(gap)], sign * i * product))
    return k, l


def convolution(left, right):
    """Use all signed corner products, with result scaled by SCALE squared."""
    result = [(0, 0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] = add(result[i + j], product_endpoints(x, y))
    return result


def verify():
    caps = signs = zeros = 0
    for d in range(2, 36):
        cosine, sine_ratio = angle_intervals(d)
        for r in range(1, d):
            hk, hl = angular_coefficients([comb(d, j) for j in range(r + 1)], cosine, sine_ratio)
            bk, bl = angular_coefficients([comb(d - 2, j) for j in range(r)], cosine, sine_ratio)
            left = convolution(hk, bl)
            right = convolution(bk, hl)
            bounds = [subtract(scale_interval(x, 2), y) for x, y in zip(left, right)]
            assert len(bounds) == 4 * r - 1
            assert bounds[0] == bounds[-1] == (0, 0)
            for j, interval in enumerate(bounds[1:-1], 1):
                assert interval[0] > 0, (d, r, j, interval)
            caps += 1
            signs += len(bounds) - 2
            zeros += 2
    print(f"Chebyshev d=2..35: {caps} caps, {signs} positive coefficients, {zeros} endpoint zeros.")


if __name__ == "__main__":
    verify()
