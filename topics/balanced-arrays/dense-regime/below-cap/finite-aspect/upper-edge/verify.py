"""Exact certificates for row-deficit switching and the interior/outer join."""
from fractions import Fraction
from math import factorial


def curvature(n, d, r, k):
    deficit = n*r - d*k
    assert 1 <= k < n*r//d and 1 <= r < d
    R = Fraction(r*(d-r), d)
    delta = (Fraction(deficit*(deficit-1), n*(n-1))/R
             + Fraction(deficit, n)/R + Fraction(2*deficit, n*r))
    delta = min(delta,(2/R+Fraction(2,r))*Fraction(deficit*(deficit-1),n*(n-1)))
    X = delta * Fraction(n+deficit+d-1, d)
    gain = (d-r) * Fraction(n*(n-1), (n+deficit-1)*(n+deficit+d-1)) * (1-X)
    return X, gain


def binomial_tail(n, d, r, k):
    """Bracket Pr(Bin(d,(k+3)/n)>r) by summation from its mode."""
    numerator = k+3
    complement = n-numerator
    mode = (d+1)*numerator//n
    unit = 2**100
    total_lo = total_hi = unit
    tail_lo = tail_hi = unit if mode > r else 0
    for step in (-1, 1):
        lo = hi = unit
        j = mode
        while 0 <= j+step <= d:
            if step == -1:
                a,b = j*complement, (d-j+1)*numerator
            else:
                a,b = (d-j)*numerator, (j+1)*complement
            lo = lo*a//b
            hi = (hi*a+b-1)//b
            j += step
            total_lo += lo
            total_hi += hi
            if j > r:
                tail_lo += lo
                tail_hi += hi
            if hi <= 4096:
                # All later outward ratios are at most one. Counting d
                # possible terms bounds both omitted sums from above.
                total_hi += d*hi
                tail_hi += d*hi
                break
    return Fraction(tail_lo,total_hi), Fraction(tail_hi,total_lo)


def main():
    n, d, r = 10**6, 250000, 127000
    degree = n*r//d
    k = degree-95
    X, gain = curvature(n,d,r,k)
    assert X < 1
    B = min(n-k, Fraction((d-r+1)*(n*r-d*k),d)+1)
    assert d*gain/(B+gain) > Fraction(11,5)
    assert sum(Fraction(11,5)**j/factorial(j) for j in range(10)) > 9
    left, right = 500000, 504000
    while left+1 < right:
        mid = (left+right)//2
        lo,hi = binomial_tail(n,d,r,mid)
        if n*hi <= Fraction(1,100):
            left = mid
        else:
            assert n*lo > Fraction(1,100)
            right = mid
    assert n*binomial_tail(n,d,r,left)[1] <= Fraction(1,100)
    assert n*binomial_tail(n,d,r,right)[0] > Fraction(1,100)
    assert left == 502387 and right == 502388
    assert left + (degree-k) == 502482 and k-left == 5518
    print("Last quota passing the binomial-tail test:", left)
    print("First quota in the certified outer interval:", k)
    print("Simple negative roots from both intervals:", left+(degree-k), "of", degree)
    print("Roots in the intervening annulus:", k-left)


if __name__ == "__main__":
    main()
