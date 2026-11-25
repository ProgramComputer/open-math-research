"""Exact coefficient ratios at the outer edge for arbitrary fixed thresholds."""
import argparse
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

ARCHIVE = Path(__file__).resolve().parents[1] / 'results' / 'outer-coefficients.json'


def multiply(a, b):
    return [sum(a[i] * b[j-i] for i in range(j+1)) for j in range(len(a))]


def power(a, k):
    result = [1] + [0]*(len(a)-1)
    while k:
        if k % 2:
            result = multiply(result, a)
        k //= 2
        if k:
            a = multiply(a, a)
    return result


def excess_coefficient(threshold, k, e):
    """[z^e] T W^k with W=j! z^-j C T."""
    j = threshold
    t = [Fraction(1)]
    for d in range(1, e+1):
        t.append(sum(t[d-b] / factorial(b) for b in range(1, min(j-1, d)+1)))
    long = [Fraction(factorial(j), factorial(j+i)) for i in range(e+1)]
    return multiply(t, power(multiply(t, long), k))[e]


def independent_excess(threshold, k, e):
    """Group the short blocks by count and the long blocks by total excess."""
    j = threshold
    # [z^a](j! z^-j C)^k via the logarithmic derivative of a k-th power.
    long = [Fraction(1)]
    for a in range(1, e+1):
        long.append(sum(((k+1)*b-a)*Fraction(factorial(j), factorial(j+b))*long[a-b]
                        for b in range(1, a+1))/a)
    short = [Fraction(1)]+[Fraction(0)]*e
    total = Fraction(0)
    for h in range(e+1):
        total += comb(k+h, h)*sum(short[a]*long[e-a] for a in range(e+1))
        short = [sum((short[a-b]/factorial(b) for b in range(1, min(j-1, a)+1)),
                     Fraction(0)) for a in range(e+1)]
    return total


def records():
    for j in range(2, 9):
        alpha = 1+Fraction(1, j+1)
        for s in range(j):
            for m in (8, 32, 128):
                ktail = []
                for h in range(3):
                    k, e = m-h, s+j*h
                    val = excess_coefficient(j, k, e)
                    if val != independent_excess(j, k, e):
                        raise ValueError((j, s, m, h))
                    ktail.append(val)
                ratios = [ktail[h]/ktail[0]/(alpha*m)**(j*h) for h in range(3)]
                yield dict(j=j, n=j*m+s, m=m, s=s, reversed_indices=[0,1,2],
                           exact_normalized_ratios=[str(x) for x in ratios],
                           predicted_limits=[str(Fraction(factorial(s), factorial(s+j*h)))
                                             for h in range(3)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = list(records())
    if args.write:
        ARCHIVE.write_text(json.dumps(data, separators=(',', ':'))+'\n')
    elif json.loads(ARCHIVE.read_text()) != data:
        raise ValueError('Exact ratio archive differs')
    print(f'{len(data)} rows, three outer coefficients per row, two exact methods.')


if __name__ == '__main__':
    main()
