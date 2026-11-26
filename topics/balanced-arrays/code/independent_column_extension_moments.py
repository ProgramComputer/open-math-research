"""Rebuild the moment determinant using implicit-series recurrences and elimination."""
from fractions import Fraction
from math import comb

from flint import arb, arb_series, ctx


THETA = Fraction(179, 543)
TERMS = 26


def ball(value):
    return arb(value.numerator) / value.denominator


def margin_residual(columns, weight, quota):
    weights = [comb(columns, k)*weight**k for k in range(6)]
    return sum(k*w for k, w in enumerate(weights)) - columns*quota*sum(weights)


def six_column_weight():
    left, right = Fraction(0), Fraction(1)
    if not margin_residual(6, left, THETA) < 0 < margin_residual(6, right, THETA):
        raise ArithmeticError("invalid bracket for the six-column weight")
    for _ in range(360):
        mid = (left+right)/2
        if margin_residual(6, mid, THETA) < 0:
            left = mid
        else:
            right = mid
    return ball(left).union(ball(right))


def inverse_weight_jet(columns, weight, variable):
    # The jth unknown enters the jth residual coefficient through this derivative alone.
    linear = sum((k-columns*ball(THETA))*k*comb(columns, k)*weight**(k-1)
                 for k in range(1, 6))
    if linear.contains(0):
        raise ArithmeticError("implicit weight derivative was not isolated")
    coefficients = [weight]
    for j in range(1, TERMS):
        residual = margin_residual(columns, arb_series(coefficients), ball(THETA)+variable)
        coefficients.append(-residual[j]/linear)
    return arb_series(coefficients)


def moments(fugacity):
    # Solve Q(theta + displacement) = Q(theta)*(1-z) one coefficient at a time.
    if fugacity[1].contains(0):
        raise ArithmeticError("inverse fugacity derivative was not isolated")
    displacement = [arb(0)]
    for j in range(1, TERMS):
        current = arb_series(displacement)
        known = sum(fugacity[k]*current**k for k in range(1, j+1))
        target = -fugacity[0] if j == 1 else 0
        displacement.append((target-known[j])/fugacity[1])
    values = [ball(Fraction(5, 7)), ball(THETA)]
    for coefficient in displacement[1:25]:
        values.append(values[-1]+coefficient)
    return values


def determinant(entries):
    product = arb(1)
    for k, row in enumerate(entries):
        pivot = row[k]
        if pivot.contains(0):
            raise ArithmeticError(f"elimination pivot {k} contains zero")
        product *= pivot
        for later in entries[k+1:]:
            multiplier = later[k]/pivot
            for j in range(k+1, len(row)):
                later[j] -= multiplier*row[j]
    return product


if __name__ == "__main__":
    ctx.prec = 1088
    ctx.cap = TERMS
    variable = arb_series([0, 1])
    six = inverse_weight_jet(6, six_column_weight(), variable)
    seven = inverse_weight_jet(7, arb(1)/2, variable)
    quota = ball(THETA)+variable
    fugacity = quota / (ball(Fraction(5, 6))-quota) * seven**7/six**6
    values = moments(fugacity)
    matrix = [[values[i+j]-values[i+j+1] for j in range(13)] for i in range(13)]
    result = determinant(matrix)
    if not ball(Fraction(-3, 10**101)) < result < ball(Fraction(-1, 10**101)):
        raise ArithmeticError(f"inconclusive determinant: {result}")
    print(result)
