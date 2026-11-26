"""Exact rational constants and sample Laurent/Hankel replay."""
from fractions import Fraction as Q
from math import comb, factorial


def verify_constants():
    peak = Q(13, 16)
    b = Q(149, 1000)
    pi_lower = Q(157, 50)
    assert Q(4, 5) + Q(4, 3)*Q(1, 5)**3/(1-Q(1, 25)) < peak
    assert peak/(2*pi_lower-peak) < b < Q(3, 20)
    assert Q(50, 17)*Q(3, 20)**3/3 < Q(1, 100)
    assert Q(100, 17)/Q(99, 100) < 6
    assert 12/(1-6*Q(3, 20)**3) < 13
    assert 13*peak < 11
    assert 11*Q(13, 10)*2*(1+Q(1, 25))**2/(1-Q(1, 25))**2 < 34
    assert 5**7 < Q(131, 20)**6
    assert Q(131, 20)*b == Q(19519, 20000)
    assert 34*Q(19519, 20000)**150 < 1
    assert 34*Q(9, 5) < 62
    rho = Q(19519, 20000)
    assert 248*(Q(7*750, 12)+1)**2*rho**750 < 1
    assert (Q(7*751+12, 7*750+12))**2*rho < 1
    assert 5*Q(2, 3)**4 < 1


def eulerian_rows(last):
    result = {1: [1]}
    for n in range(2, last+1):
        poly = [0]*n
        for j, value in enumerate(result[n-1]):
            poly[j] += (j+1)*value
            poly[j+1] += (n-1-j)*value
        result[n] = poly
    return result


def rows(k, last, eulerian):
    result = {}
    for n in range(k,last+1):
        poly = eulerian[n-1][:]
        for length in range(k,n-k+1):
            factor = comb(n-1,length-1)
            for i,a in enumerate(eulerian[length-1]):
                for j,b in enumerate(result[n-length]):
                    poly[i+j+1] += factor*a*b
        result[n] = poly
    return result


def moments(p, q, through):
    def normalized_translation(poly):
        total = sum(poly)
        return [Q((-1)**h * sum(comb(i,h)*poly[i]
                               for i in range(h,len(poly))), total)
                for h in range(through+1)]

    numerator = normalized_translation(p)
    denominator = normalized_translation(q)
    result = []
    for h,a in enumerate(numerator):
        result.append(a-sum(denominator[j]*result[h-j] for j in range(1,h+1)))
    return result


def bernoulli(last):
    result = [Q(1)]
    for j in range(1,last+1):
        result.append(-sum(comb(j+1,h)*result[h] for h in range(j))/(j+1))
    return result


def verify_positive(mom, m):
    a = [[mom[i+j] for j in range(m+1)] for i in range(m+1)]
    for j in range(m+1):
        assert a[j][j] > 0
        for i in range(j+1,m+1):
            factor = a[i][j]/a[j][j]
            for h in range(j+1,m+1):
                a[i][h] -= factor*a[j][h]


def verify_samples():
    eulerian = eulerian_rows(3*24)
    bern = bernoulli(24)
    total = 0
    for k in range(3,25):
        polys = rows(k,3*k+1,eulerian)
        d = k+k%2
        m = max(d//2,7*k//12)
        fraction = [Q(1)] + [Q(0)]*(k-1)
        for n in range(k,3*k+2):
            fraction.append(sum(fraction[:n-k+1])/n)
        for n in sorted({2*k-1,2*k,2*k+2,3*k}):
            mom = moments(polys[n],polys[n+1],2*m)
            assert mom[:d] == [Q(1,j+1) for j in range(d)]

            def expectation(n,j):
                return fraction[n-j]/(j*fraction[n])

            def leading(n):
                return (expectation(n,k) if k%2==0 else
                        expectation(n,k+1)-k*expectation(n,k))

            predicted = -bern[d]/factorial(d)*(leading(n)-leading(n+1))
            assert mom[d]-Q(1,d+1) == predicted
            assert abs(predicted) < Q(1,4)**d
            verify_positive(mom,m)
            total += 1
    print(f"Exact exceptional moments and positive Hankel pivots on {total} sample pairs.")


if __name__ == "__main__":
    verify_constants()
    print("All rational bounds for the uniform extension passed.")
    verify_samples()
