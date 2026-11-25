"""Certified constants and exact finite prefix for ordered threshold four."""

import argparse
from fractions import Fraction as Q
from math import comb

from flint import arb, ctx, fmpq, fmpq_poly, fmpz_poly


def ball(q):
    return arb(fmpq(q.numerator, q.denominator))


def exclude_low_horizontal_zeros():
    """Cover x in [-2,2] on Im z=4/3 and exclude every v in [0,1/12]."""
    ctx.prec = 120
    y = ball(Q(4, 3))
    sine, cosine = y.sin(), y.cos()
    if not cosine > ball(Q(1, 5)) or not -cosine.log() < ball(Q(8, 5)):
        raise ArithmeticError("Cosine bounds failed")
    stack = [(Q(-2), Q(2), 0)]
    checked = 0
    while stack:
        low, high, depth = stack.pop()
        x = arb(ball((low+high)/2), ball((high-low)/2))
        exp_x = x.exp()
        v = 1 - y*((x+1)**2/2 + arb(1)/2 - y*y/6)/(exp_x*sine)
        real = (1-v)*exp_x*cosine - (1+x+(x*x-y*y)/2+(x**3-3*x*y*y)/6) + 2*v
        if v < 0 or v > ball(Q(1, 12)) or not real.contains(0):
            checked += 1
        elif depth < 24:
            middle = (low+high)/2
            stack.extend(((low, middle, depth+1), (middle, high, depth+1)))
        else:
            raise ArithmeticError(f"Unresolved interval on Im z=4/3: {low} to {high}")
    return checked


def first_block_rows(limit):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([1])]
    for n in range(1, limit+1):
        small = sum((comb(n, s)*rows[n-s] for s in range(1, min(3, n)+1)),
                    fmpz_poly([]))
        large = sum((comb(n, s)*rows[n-s] for s in range(4, n+1)), fmpz_poly([]))
        rows.append(small+t*large)
    return rows


def delayed_rows(limit):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([value]) for value in (1, 1, 3, 13)]
    for n in range(3, limit):
        current, previous, earlier, delay = rows[n], rows[n-1], rows[n-2], rows[n-3]
        d2, d3 = comb(n, 2), comb(n, 3)
        rows.append((n+1)*current + 2*t*current.derivative() + (n+d2)*previous
                    + (d2+d3)*earlier + d3*t*(delay+(t-1)*delay.derivative()))
    return rows


def negative_remainder(left, right):
    rem = (-(fmpq_poly(left) % fmpq_poly(right))).numer()
    return rem // rem.content() if rem else rem


def strict_oriented_pair(old, new):
    if new.degree() == 0:
        return
    left = old
    if old.degree() == new.degree():
        left = -negative_remainder(old, new)
    a, b = new, left
    while b:
        if b.degree() != a.degree()-1 or b.leading_coefficient() <= 0:
            raise ArithmeticError("Invalid oriented Euclidean remainder sequence")
        a, b = b, negative_remainder(a, b)
    if a.degree() != 0:
        raise ArithmeticError("A consecutive pair has a nonconstant common factor")


def finite_prefix(limit):
    rows = first_block_rows(limit)
    if rows != delayed_rows(limit):
        raise ArithmeticError("Independent coefficient recurrences disagree")
    for n, row in enumerate(rows):
        if row.degree() != n//4 or any(c <= 0 for c in row):
            raise ArithmeticError(f"Unexpected row {n}")
        if n:
            strict_oriented_pair(rows[n-1], row)
    return len(rows)


def numerical_margins():
    pi = arb.pi()
    if not (ball(Q(31, 10)) < pi < ball(Q(16, 5))
            and arb(1).exp() < ball(Q(30, 11))
            and ball(Q(3, 5)).exp() < 2 and ball(Q(16, 5)).exp() < 28
            and ball(Q(4, 5)).exp() < 3):
        raise ArithmeticError("Invalid wide-strip or circular estimates")
    if not (arb(2).exp() < 8 and arb(2).log() > ball(Q(2, 3))
            and arb(4000).log() < 9):
        raise ArithmeticError("Invalid Jensen constants")
    if not (Q(120, 36)-Q(16, 5) >= Q(1, 8)
            and 224*Q(2, 3)**120 < Q(1, 100)):
        raise ArithmeticError("Invalid effective cosine margin")
    if not (ball(Q(5, 16)).exp() < ball(Q(11, 8))
            and ball(Q(4, 3)).log() < ball(Q(3, 10))
            and ball(Q(64, 19)).log() < ball(Q(5, 4))):
        raise ArithmeticError("Invalid analytic branch constants")
    if not (Q(3, 8)*(1+Q(5, 4)**4/5) < Q(1, 4)*(Q(7, 5)-Q(1, 4))**2*Q(7, 4)):
        raise ArithmeticError("Rouché inequality failed")

    h = Q(3, 50)
    if not (Q(3, 10)*Q(5, 7)+Q(49, 300)*h+Q(3, 10)*4**3*h*h/(1-4*h) < Q(1, 3)
            and Q(49, 150)+Q(3, 5)*4**6*h**4/(1-(4*h)**4) < Q(2, 5)
            and Q(33, 100)+Q(5, 2)*4**6*h**4/(1-(4*h)**4) < Q(1, 2)):
        raise ArithmeticError("Cauchy inequalities failed")
    for hi, gap in [(h, Q(3, 10)), (Q(1, 2), Q(7, 25)), (Q(1), Q(1, 5)), (Q(2), Q(3, 100))]:
        numerator = Q(1, 2)-Q(5, 48)*hi**2
        if not (numerator > 0 and numerator**2 > gap**2*(Q(41, 16)+Q(7, 8)*hi**2)):
            raise ArithmeticError("Refined modulus gap failed")
    for lo, gap in [(h, Q(7, 25)), (Q(1, 2), Q(1, 5)), (Q(1), Q(3, 100))]:
        if (200*gap-Q(16, 5))*lo <= 2:
            raise ArithmeticError("Bulk suppression failed")
    if not ((-arb(2)).exp()*arb(2).sqrt() < ball(Q(1, 4))
            and Q(2, 3)*h+Q(8, 600) < Q(3, 50)
            and Q(7, 10)*Q(47, 50)-Q(33, 20)*16/200 > Q(1, 2)
            and 56*Q(5, 4)**3*h*(h+Q(4, 200))**2*Q(2, 3)**200 < Q(1, 100)):
        raise ArithmeticError("Determinant margins failed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=200)
    args = parser.parse_args()
    if args.limit < 199:
        parser.error("at least rows 0 through 199 are needed to cover consecutive pairs")
    interval_count = exclude_low_horizontal_zeros()
    numerical_margins()
    row_count = finite_prefix(args.limit)
    print(f"Excluded every low-pole crossing by {interval_count} certified Arb intervals.")
    print(f"Verified {row_count} exact rows and {row_count-1} strict oriented pairs.")


if __name__ == "__main__":
    main()
