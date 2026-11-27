from fractions import Fraction
from math import comb


def linear_product(a, b):
    a, b = Fraction(a), Fraction(b)
    return [a*b, a+b, Fraction(1)]


def polynomial_sum(*terms):
    result = [Fraction(0)] * max(len(coefficients) for _, coefficients in terms)
    for multiplier, coefficients in terms:
        for i, coefficient in enumerate(coefficients):
            result[i] += multiplier * coefficient
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def value(coefficients, x):
    total = Fraction(0)
    for coefficient in reversed(coefficients):
        total = total*x + coefficient
    return total


def actual_rows(j, alphabet, maximum):
    rows = [[1]]
    for n in range(1, maximum+1):
        row = [0] * (1+n//j)
        for size in range(1, min(n, alphabet)+1):
            weight = comb(alphabet, size)
            mark = int(size >= j)
            for k, coefficient in enumerate(rows[n-size]):
                row[k+mark] += weight*coefficient
        rows.append(row)
    return rows


def long_state(rows, j, n, b):
    return polynomial_sum(*[(comb(b-1, size-1), rows[n-size])
                            for size in range(j, min(b,n)+1)])


def scaled_difference(rows, j, n, b):
    return polynomial_sum((comb(b-1,j-1), long_state(rows,j,n,b+1)),
                          (-comb(b,j-1), long_state(rows,j,n,b)))


def discriminant(coefficients):
    constant, linear, quadratic = coefficients
    return linear**2-4*constant*quadratic


def check():
    g2 = linear_product(2, 5)
    g3 = linear_product(Fraction(39,10), 6)
    g4 = linear_product(Fraction(79,20), Fraction(601,100))
    p = polynomial_sum((100, linear_product(1, 4)))
    d2 = polynomial_sum((1, g3), (-1, g2))
    d3 = polynomial_sum((1, g4), (-1, g3))
    assert all(c > 0 for c in d2+d3)
    assert d2[0]/d2[1] < d3[0]/d3[1]
    h3 = polynomial_sum((1, p), (Fraction(1,2), g2))
    h4 = polynomial_sum((1, p), (Fraction(1,3), g2), (Fraction(2,3), g3))
    cut = Fraction(-4003,1000)
    assert value(h3,cut) < 0 < value(h4,cut)
    assert value(h4,-3) < 0 < value(h4,0)
    print('Generic normalized update H3(cut), H4(cut):', value(h3,cut), value(h4,cut))

    j, alphabet, n, b = 2, 5, 4, 4
    rows = actual_rows(j,alphabet,n+1)
    q = polynomial_sum(*[(1,long_state(rows,j,n,a)) for a in range(j,alphabet+1)])
    d = scaled_difference(rows,j,n+1,b)
    assert q == [305,100] and d == [193,60]
    bad = polynomial_sum((1,[0]+q),(5,d))
    assert bad == [965,605,100] and discriminant(bad) == -19975
    for smaller in (3,4):
        rows = actual_rows(j,smaller,n+1)
        q = polynomial_sum(*[(1,long_state(rows,j,n,a)) for a in range(j,smaller+1)])
        for c in range(j,smaller):
            d = scaled_difference(rows,j,n+1,c)
            assert 0 < d[0]/d[1] < q[0]/q[1]
    print('Actual split-compatibility witness:', bad, 'discriminant', discriminant(bad))

    rows = actual_rows(2,4,5)
    second_difference = polynomial_sum((Fraction(1,3),long_state(rows,2,5,4)),
                                       (-1,long_state(rows,2,5,3)),
                                       (1,long_state(rows,2,5,2)))
    assert second_difference == [Fraction(4,3)]
    bad = polynomial_sum((1,rows[4]), (400, second_difference))
    assert discriminant(bad) == -10623
    print('Actual full second-difference cone witness discriminant:', discriminant(bad))

    p1, p2, oldest = [1,1], [2,1], [3,1]
    output = polynomial_sum((3,p1),(3,p2),(1,[0]+oldest))
    assert output == [9,9,1] and value(output,-1) == 1
    print('Generic last-row output:', output, 'value at old zero:', value(output,-1))


if __name__ == '__main__':
    check()
