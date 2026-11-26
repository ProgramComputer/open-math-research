"""Rigorous moment obstruction for adding a seventh column at row cap five."""
from fractions import Fraction
from math import comb

from flint import arb, arb_mat, arb_series, ctx


def ball(value):
    return arb(value.numerator) / value.denominator


def mean_quota(x, columns):
    weights = [comb(columns, i) * x**i for i in range(6)]
    return sum(i * weight for i, weight in enumerate(weights)) / (columns * sum(weights))


def inverse_weight_bracket(quota):
    lo, hi = Fraction(0), Fraction(1)
    if not mean_quota(lo, 6) < quota < mean_quota(hi, 6):
        raise ArithmeticError("invalid initial bracket")
    for _ in range(200):
        mid = (lo + hi) / 2
        if mean_quota(mid, 6) < quota:
            lo = mid
        else:
            hi = mid
    return ball(lo).union(ball(hi))


def centered_reversion(series, terms):
    # The underlying centered function has exactly zero constant term.
    return arb_series([0] + [series[j] for j in range(1, terms)], prec=terms).reversion()


def verify():
    ctx.prec = 640
    ctx.cap = terms = 26
    x7 = Fraction(1, 2)
    quota = mean_quota(x7, 7)
    if quota != Fraction(179, 543):
        raise ArithmeticError("unexpected exact target quota")
    x6 = inverse_weight_bracket(quota)
    weights = []
    for columns, weight in [(6, x6), (7, ball(x7))]:
        quota_jet = mean_quota(arb_series([weight, 1], prec=terms), columns)
        weights.append(weight + centered_reversion(quota_jet, terms))
    x6_jet, x7_jet = weights
    quota_jet = arb_series([ball(quota), 1], prec=terms)
    fugacity = quota_jet / (ball(Fraction(5, 6)) - quota_jet) * x7_jet**7 / x6_jet**6
    if not (fugacity[0] > 0 and fugacity[1] > 0):
        raise ArithmeticError("failed to isolate the positive inverse jet")
    # Revert z = 1 - q(quota + u) / q(quota), then form quota(q(1-z))/(1-z).
    displacement = centered_reversion(-fugacity / fugacity[0], terms)
    generating = (ball(quota) + displacement) / arb_series([1, -1], prec=terms)
    moments = [ball(Fraction(5, 7))] + [generating[j] for j in range(terms)]
    localizing = arb_mat([
        [moments[i+j] - moments[i+j+1] for j in range(13)]
        for i in range(13)
    ])
    determinant = localizing.det()
    if not ball(Fraction(-3, 10**101)) < determinant < ball(Fraction(-1, 10**101)):
        raise ArithmeticError(f"failed to certify negative determinant: {determinant}")
    print(f"quota = {quota}")
    print(f"13 by 13 localizing determinant = {determinant}")


if __name__ == "__main__":
    verify()
