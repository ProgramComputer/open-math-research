"""Exact checks for the effective far-left Catalan edge argument."""

from fractions import Fraction as Q
from math import comb, prod

from flint import fmpq, fmpq_poly, fmpz_poly


def coefficient_row(n):
    coefficients = []
    for k in range((n-1)//2+1):
        entry, rem = divmod(comb(n-k,k)*comb(2*n-3*k,n-2*k-1), n-k)
        if rem:
            raise ArithmeticError("binomial formula gave a nonintegral result")
        coefficients.append(entry)
    return fmpz_poly(coefficients)(fmpz_poly([-1,1]))


def largest_magnitude_polynomial(n):
    row = coefficient_row(n)
    row = row(fmpz_poly([0,-1]))
    return -row if row.degree()%2 else row


def sturm(row):
    first = fmpq_poly(row)
    if not first.degree():
        return [first]
    sequence = [first, first.derivative()]
    while remainder := -(sequence[-2] % sequence[-1]):
        sequence.append(remainder)
    if sequence[-1].degree() != 0:
        raise ArithmeticError("prefix polynomial has repeated roots")
    return sequence


def sign_changes(values):
    signs = [value > 0 for value in values if value != 0]
    return sum(a != b for a,b in zip(signs, signs[1:]))


def root_bracket(sequence, rank):
    upper = fmpq(1)
    lower = fmpq(0)
    changes_infinity = sign_changes(p.leading_coefficient() for p in sequence)
    if sign_changes(p(0) for p in sequence)-changes_infinity != sequence[0].degree():
        raise ArithmeticError("prefix misses a real root in the required interval")
    while sign_changes(p(upper) for p in sequence)-changes_infinity >= rank:
        upper *= 2
    for _ in range(56):
        middle = (lower+upper)/2
        count_above = sign_changes(p(middle) for p in sequence)-changes_infinity
        if count_above < rank:
            upper = middle
        else:
            lower = middle
    return lower, upper


def exact_prefix(last_even):
    rows = {n: sturm(largest_magnitude_polynomial(n)) for n in range(3,last_even+2)}
    odd = {n: [root_bracket(sequence, rank)
               for rank in range(1,min(2,sequence[0].degree())+1)]
           for n,sequence in rows.items() if n%2}
    for n in range(4,last_even+1,2):
        lower,upper = root_bracket(rows[n],1)
        for neighbor in (n-1,n+1):
            first,*rest = odd[neighbor]
            if not upper < first[0]:
                raise ArithmeticError((n, neighbor, "first odd root order failed"))
            if rest and not rest[0][1] < lower:
                raise ArithmeticError((n, neighbor, "second odd root order failed"))
    return len(rows)


def margins():
    m = fmpz_poly([20,1])
    ratios = ((1,Q(7,100),Q(11,500),8), (2,Q(4,25),Q(1,15),Q(3,2)))
    for delta, second, subsequent, radius in ratios:
        num = (m-1)*(m+delta+1)*(m+delta+2)*prod(m+2*delta+i for i in range(4,7))
        den = m*(m+delta)*(m+delta+3)*prod(m+2*delta+i for i in range(1,4))
        d = lambda j: (delta+2*j)*(delta+2*j-1)**2*(delta+2*j-2)
        if not all(c>0 for c in second.numerator*d(2)*den-second.denominator*d(1)*num):
            raise ArithmeticError((delta, "second-ratio margin failed"))
        ratio_at_20 = (1+Q(2,20+delta))*Q(d(1),d(3))*(1+Q(6,21+2*delta))**3
        if not ratio_at_20 < subsequent:
            raise ArithmeticError((delta, "later-ratio margin failed"))
        if not second*radius**2/(1-subsequent*radius) < radius-1:
            raise ArithmeticError((delta, "circle margin failed"))
    if not 6*Q(21,22)*Q(24,26)*Q(24,27)>4 or not 6*Q(24,27)>4:
        raise ArithmeticError("parity-ratio margin failed")


if __name__ == "__main__":
    margins()
    print(f"Exact rational brackets verified both odd-neighbor comparisons for each even row 4..42 ({exact_prefix(42)} rows).")
