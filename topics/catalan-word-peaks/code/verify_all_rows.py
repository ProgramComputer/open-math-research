"""Exact constants and prefix check for the Catalan bulk real-rootedness result."""
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
import json
import sys

from flint import fmpq_poly, fmpz_poly


def margins():
    n = 150
    local = ((Q(2*n,5)+9)*Q(3,2)/(n-Q(3,2))
             +(Q(2*n,5)+Q(4,5))*Q(15,4)/((n-Q(3,2))*(n-Q(5,2))))
    if not local < Q(71,100):
        raise ArithmeticError('principal beta-moment bound')
    for n in range(150,154):
        if not 60*n*Q(8,9)**(n-(n+3)//4) < Q(1,50):
            raise ArithmeticError('principal beta-tail bound')
    n = 150
    if not (Q(n+4,n)*Q(8,9)**3 < 1 and
            1+Q(3,4)*n/(n-6) < Q(9,5) and
            1+(1+Q(n,4))*Q(3,4)/(n-Q(3,2)) < Q(6,5)):
        raise ArithmeticError('beta-tail monotonicity or remote moments')
    if not (Q(89,100)*(Q(11,8)*Q(31,10)-1) > Q(29,10) and
            Q(89,100)*Q(3,4)*Q(31,10) > 2 and
            sum(Q(58,15)**j/factorial(j) for j in range(11)) > 40):
        raise ArithmeticError('angular or exponential comparison')
    for n in range(150,154):
        if not 60*n*n*Q(6,7)**(n-(n+3)//4) < Q(1,20):
            raise ArithmeticError('covariance tail bound')
    n = 150
    if not Q(n+4,n)**2*Q(6,7)**3 < 1:
        raise ArithmeticError('covariance tail monotonicity')

    def moment(j):
        return prod((Q(3,2)+k)/(n-Q(3,2)-k) for k in range(j))
    def tilted_moment_bound(j):
        return moment(j+1)+Q(3,2*n)*moment(j)
    variance = Q(3,2)*n/((n-Q(3,2))**2*(n-Q(5,2)))
    etilt = (n-Q(1,2))/(n+1)
    near_loss = 11*moment(1)+(1+Q(11*n,8))*moment(2)+Q(n,8)*moment(3)+Q(1,20*n)
    near_cov = (Q(n,8)*variance + 11*tilted_moment_bound(1)
                +(1+Q(11*n,8))*tilted_moment_bound(2)
                +Q(n,8)*tilted_moment_bound(3)+Q(1,20*n))
    far_cov = ((Q(n,2)+11)*tilted_moment_bound(1)
               +(Q(n,2)+1)*tilted_moment_bound(2)+Q(1,20*n))
    if not (near_loss < Q(3,20) and n*near_cov < etilt and n*far_cov < 4*etilt):
        raise ArithmeticError('consecutive beta-moment bound')
    if not ((Q(27,100)**2-Q(1,25)**2)>Q(1,4)**2
            and Q(7,10)*Q(1,4)>Q(4,n)+Q(2,25)
            and Q(17,20)**2-Q(1,100*n)**2>Q(4,5)**2
            and Q(6,5)*n*Q(1,2)**n < Q(1,100*n)):
        raise ArithmeticError('consecutive sign margin')


def sturm(p):
    a, b = p, p.derivative()
    signs = []
    while a:
        signs.append((a.degree(), a.leading_coefficient() > 0, a[0] > 0 if a[0] else None))
        if not b:
            break
        r = -(fmpq_poly(a) % fmpq_poly(b)).numer()
        a, b = b, r // r.content() if r else r
    minus = [positive != bool(degree%2) for degree,positive,_ in signs]
    at_zero = [value for _,_,value in signs if value is not None]
    variation = lambda signs: sum(s != t for s,t in zip(signs,signs[1:]))
    if signs[-1][0] != 0 or variation(minus)-variation(at_zero) != p.degree():
        raise ArithmeticError('unexpected negative simple-root count')


def strict_pair(old, new):
    if new.degree() == 0:
        return
    def rem(left, right):
        r = (-(fmpq_poly(left) % fmpq_poly(right))).numer()
        return r // r.content() if r else r
    a, b = new, old if old.degree() < new.degree() else -rem(old,new)
    while b:
        if b.degree() != a.degree()-1 or b.leading_coefficient() <= 0:
            raise ArithmeticError('strict orientation in the finite prefix failed')
        a,b = b,rem(a,b)
    if a.degree() != 0:
        raise ArithmeticError('consecutive prefix rows have a common zero')


def enumerate_prefix(last):
    t = fmpz_poly([0,1])
    rows = [fmpz_poly([1])]
    square = []
    for n in range(1,last+1):
        square.append(sum((rows[i]*rows[n-1-i] for i in range(n)), fmpz_poly([])))
        p = square[-1]
        if n >= 2:
            p += (1-t)*(rows[n-2]-square[n-2])
        rows.append(p)
    return rows


def main(path):
    margins()
    with Path(path).open() as input_data:
        archived = [json.loads(line) for line in input_data]
    plus_shift = fmpz_poly([-1,1])
    if [r['n'] for r in archived] != list(range(151)):
        raise ArithmeticError('wrong prefix size')
    rows = enumerate_prefix(150)
    for n, (row, record) in enumerate(zip(rows, archived)):
        if n:
            coeff = []
            for k in range((n-1)//2+1):
                a, b = divmod(comb(n-k,k)*comb(2*n-3*k,n-2*k-1),n-k)
                if b:
                    raise ArithmeticError('nonintegral binomial entry')
                coeff.append(a)
            if row != fmpz_poly(coeff)(plus_shift):
                raise ArithmeticError(f'independent binomial count at n={n}')
        if list(row) != record['coefficients'] or len(row) != max(0,(n-1)//2)+1:
            raise ArithmeticError(f'archive mismatch at n={n}')
        if any(c <= 0 for c in row):
            raise ArithmeticError(f'coefficient sign at n={n}')
        sturm(row)
        if n:
            strict_pair(rows[n-1],row)
    print('Verified exact margins, 151 full simple-negative root counts and 150 strict oriented pairs.')


if __name__ == '__main__':
    main(sys.argv[1])
