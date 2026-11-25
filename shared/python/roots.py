"""Exact polynomial diagnostics. Coefficient lists are in ascending order."""
from fractions import Fraction

from flint import fmpq_poly, fmpz_poly, fmpz_mat


def _poly(coeffs):
    p = fmpz_poly(list(coeffs))
    if not p:
        raise ValueError("the zero polynomial has no finite root count")
    return p


def _primitive(p):
    return p // p.content() if p else p


def _negative_remainder(a, b):
    # FLINT's rational numerator clears a positive common denominator.
    return _primitive(-(fmpq_poly(a) % fmpq_poly(b)).numer())


def _sign(x):
    return int(x > 0) - int(x < 0)


def _variations(signs):
    signs = [s for s in signs if s]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def newton_min(coeffs):
    """Minimum normalized Newton ratio as (index, Fraction), or None."""
    m = len(coeffs) - 1
    if any(x <= 0 for x in coeffs):
        raise ValueError("Newton ratio diagnostic expects positive coefficients")
    return min(((k, Fraction(k*(m-k)*coeffs[k]**2,
                             (k+1)*(m-k+1)*coeffs[k-1]*coeffs[k+1]))
                for k in range(1, m)), key=lambda v: v[1], default=None)


def root_report(coeffs):
    p = _poly(coeffs)
    s = _primitive(p // p.gcd(p.derivative()))
    a, b = s, _primitive(s.derivative())
    signs = [(a.degree(), _sign(a.leading_coefficient()))]
    while b:
        signs.append((b.degree(), _sign(b.leading_coefficient())))
        a, b = b, _negative_remainder(a, b)
    left = _variations([(-1)**d * sign for d, sign in signs])
    right = _variations([sign for d, sign in signs])
    count = left - right
    return dict(method="primitive rational Sturm", degree=p.degree(),
                squarefree_degree=s.degree(), v_minus=left, v_plus=right,
                distinct_real_roots=count, real_rooted=count == s.degree())


def interlaces(left, right):
    """SymCat's weak, oriented interleaving, including common multiplicities."""
    a, b = fmpz_poly(list(left)), fmpz_poly(list(right))
    if not a or not b:
        return True
    if b.degree() - a.degree() not in (0, 1):
        return False
    if a.leading_coefficient() < 0:
        a = -a
    if b.leading_coefficient() < 0:
        b = -b
    common = a.gcd(b)
    if common.degree() and not root_report(common)["real_rooted"]:
        return False
    a, b = a // common, b // common
    if b.degree() == 0:
        return True
    if a.degree() == b.degree():
        # Subtracting a multiple of b keeps the residues of a/b.
        a = -_negative_remainder(a, b)
    # A strictly interlacing numerator of b has degree deg(b)-1 with
    # positive residues. Negative Euclidean remainders repeat this property.
    while b.degree() > 0:
        if a.degree() != b.degree()-1 or a.leading_coefficient() <= 0:
            return False
        b, a = a, _negative_remainder(b, a)
    return True


def laguerre_at(coeffs, x):
    """L_1(x)=(p')²−p p''; a negative value at a rational x refutes RR."""
    p = fmpq_poly(_poly(coeffs))
    x = Fraction(x)
    from flint import fmpq
    point = fmpq(x.numerator, x.denominator)
    q = p.derivative()
    return Fraction(str(q(point)**2 - p(point)*q.derivative()(point)))


def hermite_minors(coeffs):
    """Leading Hermite minors of the square-free part after scaling the roots.

    Scaling each root by the leading coefficient gives a monic integer
    polynomial. Its Newton sums form the Hermite matrix. Positive definiteness
    is equivalent to all roots real because the square-free trace form is
    nonsingular. Return det(H[:i,:i]) for i=1,...,deg.
    """
    p = _poly(coeffs)
    p = p // p.gcd(p.derivative())
    m = p.degree()
    lead = int(p.leading_coefficient())
    if not m:
        return []
    c = [1] + [int(p[m-i])*lead**(i-1) for i in range(1,m+1)]
    sums = [m]
    for k in range(1, 2*m-1):
        value = sum(c[j]*sums[k-j] for j in range(1, min(k-1,m)+1))
        sums.append(-value - (k*c[k] if k <= m else 0))
    return [int(fmpz_mat([[sums[i+j] for j in range(k)] for i in range(k)]).det())
            for k in range(1, m+1)]


def same_polynomial(left, right):
    return fmpz_poly(list(left)) == fmpz_poly(list(right))


def toeplitz_minor(coeffs,rows,columns):
    """Minor indexed by strictly increasing row/column indices, with zero padding."""
    if len(rows)!=len(columns) or any(b<=a for indices in (rows,columns)
                                      for a,b in zip(indices,indices[1:])):
        raise ValueError("expected ordered indices of a square minor")
    return int(fmpz_mat([[coeffs[j-i] if 0<=j-i<len(coeffs) else 0 for j in columns]
                         for i in rows]).det())


def discriminant(coeffs):
    return int(_poly(coeffs).discriminant())
