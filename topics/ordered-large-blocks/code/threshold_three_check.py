"""Exact finite prefix and rational constants for the ordered threshold-three theorem."""

from fractions import Fraction as Q
from math import comb, factorial

from flint import fmpq_poly, fmpz_poly

CUTOFF = 94


def first_block_rows(limit):
    t = fmpz_poly([0, 1])
    rows = [fmpz_poly([1]), fmpz_poly([1])]
    for n in range(2, limit+1):
        small = n*rows[n-1] + comb(n, 2)*rows[n-2]
        large = sum((comb(n, s)*rows[n-s] for s in range(3, n+1)), fmpz_poly([]))
        rows.append(small+t*large)
    return rows


def delayed_rows(limit):
    t = fmpz_poly([0, 1])
    rows = list(map(lambda c: fmpz_poly([c]), (1, 1, 3)))
    for n in range(2, limit):
        current, previous, earlier = rows[n], rows[n-1], rows[n-2]
        d = comb(n, 2)
        rows.append((n+1)*current + 2*t*current.derivative() + (n+d)*previous
                    + d*t*(earlier+(t-1)*earlier.derivative()))
    return rows


def primitive(poly):
    return poly // poly.content() if poly else poly


def negative_remainder(left, right):
    return primitive((-(fmpq_poly(left) % fmpq_poly(right))).numer())


def variations(signs):
    return sum(a != b for a, b in zip(signs, signs[1:]))


def simple_real_certificate(poly):
    if poly.degree() == 0:
        return
    a, b = poly, primitive(poly.derivative())
    degree_sign = []
    while b:
        degree_sign.append((a.degree(), 1 if a.leading_coefficient() > 0 else -1))
        a, b = b, negative_remainder(a, b)
    degree_sign.append((a.degree(), 1 if a.leading_coefficient() > 0 else -1))
    if a.degree() != 0:
        raise ArithmeticError("A multiple root was detected")
    left = [(-1)**d * sign for d, sign in degree_sign]
    right = [sign for _, sign in degree_sign]
    if variations(left)-variations(right) != poly.degree():
        raise ArithmeticError("A nonreal root was detected")


def strict_oriented_pair(old, new):
    if new.degree() == 0:
        return
    left = old
    if old.degree() == new.degree():
        left = -negative_remainder(old, new)
    a, b = new, left
    while b:
        if b.degree() != a.degree()-1 or b.leading_coefficient() <= 0:
            raise ArithmeticError("The strict oriented remainder test failed")
        a, b = b, negative_remainder(a, b)
    if a.degree() != 0:
        raise ArithmeticError("Nonconstant common factor in consecutive rows")


def exp_upper(x):
    total = sum(x**i/factorial(i) for i in range(8))
    return total + x**8/factorial(8)/(1-x/9)


def check_rational_constants():
    if not 3*Q(23, 20)**2 < 4 < 3*Q(7, 6)**2:
        raise ArithmeticError("Invalid bounds on 2/sqrt(3)")
    if not exp_upper(Q(7, 6)) < Q(129, 40) or not exp_upper(Q(2)) < 8:
        raise ArithmeticError("Invalid rational exponential bound")
    if not 1+Q(9, 5)+Q(9, 5)**2/2 > Q(100, 23):
        raise ArithmeticError("Invalid bound on the negative pole")
    for j, upper in enumerate((Q(8, 5), Q(9, 5), Q(2), Q(21, 10))):
        if not (upper-Q(13, 20))**2 > Q(11, 25)+4*Q(j+1, 10):
            raise ArithmeticError(f"Invalid square-root comparison in bin {j}")
        if not (upper-1)**2/(upper+1) < Q(38, 221)+Q(j, 10):
            raise ArithmeticError(f"Invalid phase comparison in bin {j}")
    if not Q(18, 5)*Q(3, 10)**(CUTOFF+1) < Q(1, 16):
        raise ArithmeticError("Invalid residue or interlacing margin")


def main():
    rows = first_block_rows(CUTOFF)
    if rows != delayed_rows(CUTOFF):
        raise ArithmeticError("Independent exact coefficient recurrences disagree")
    check_rational_constants()
    for n, row in enumerate(rows):
        if row.degree() != n//3 or any(c <= 0 for c in row):
            raise ArithmeticError(f"Incorrect degree or coefficient signs at row {n}")
        simple_real_certificate(row)
        if n:
            strict_oriented_pair(rows[n-1], row)
    print(f"Verified {len(rows)} rows, {len(rows)-1} strict oriented pairs, and the rational constants.")


if __name__ == "__main__":
    main()
