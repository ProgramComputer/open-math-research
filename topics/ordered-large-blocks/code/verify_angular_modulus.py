"""Exact angular comparisons on the unit disk for the ordered thresholds 4 to 12."""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as Q
from math import comb, factorial
import json
from pathlib import Path

ARCHIVE = Path(__file__).resolve().parents[1] / 'results' / 'angular-modulus.json'


def chebyshev(limit):
    result = [[1], [0, 1]]
    for _ in range(2, limit+1):
        a = [0]+[2*c for c in result[-1]]
        for i,c in enumerate(result[-2]):
            a[i] -= c
        result.append(a)
    return result


def difference_polynomial(j, v):
    """Coefficient of r^a u^b in (|A(theta)|²-|A(phi_v)|²)/(2r(v-u))."""
    t = chebyshev(j-1)
    result = defaultdict(Q)
    for k in range(1,j):
        radial = {k-1: Q(1,factorial(k))}
        for h in range(1,j-k):
            radial[2*h+k-1] = -Q(1,factorial(h)*factorial(h+k))
        for degree, lead in enumerate(t[k]):
            for power in range(degree):
                c = lead * v**(degree-1-power)
                for a,value in radial.items():
                    result[a,power] += value*c
    return {k: v for k,v in result.items() if v}


def minimum_bernstein(polynomial, left, right):
    scaled = defaultdict(Q)
    for (a,b),value in polynomial.items():
        for hull_power in range(b+1):
            scaled[a,hull_power] += (value*comb(b,hull_power)*left**(b-hull_power)
                                     *(right-left)**hull_power)
    degree_r = max(a for a,b in polynomial)
    degree_u = max(b for a,b in polynomial)
    bounds = []
    for i in range(degree_r+1):
        for h in range(degree_u+1):
            coeff = sum(c*Q(comb(i,a),comb(degree_r,a))*Q(comb(h,b),comb(degree_u,b))
                        for (a,b),c in scaled.items() if a<=i and b<=h)
            bounds.append(coeff)
    return min(bounds)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    records = []
    for j in range(4,13):
        v = Q(7,10) if j==4 else Q(4,5)
        poly = difference_polynomial(j,v)
        ends = (Q(-1),Q(-1,2),Q(0),Q(1,2))
        for l,r in zip(ends,ends[1:]):
            bound = minimum_bernstein(poly,l,r)
            if bound <= Q(1,6):
                raise ArithmeticError(f'Angular comparison at threshold {j}, interval {l}..{r}')
            records.append(dict(j=j,v=str(v),u=[str(l),str(r)],minimum=str(bound)))
    if args.write:
        ARCHIVE.write_text(json.dumps(records,indent=2)+'\n')
    elif records != json.loads(ARCHIVE.read_text()):
        raise ValueError('Bernstein archive differs')
    print('All 27 bivariate Bernstein minima exceed 1/6.')


if __name__ == '__main__':
    main()
