from fractions import Fraction
from math import factorial


def coefficients(last):
    a = [Fraction(1)]
    for n in range(1, last+1):
        a.append(sum(a[n-size]/factorial(size) for size in range(1, n+1)))
    c = [(a[n]+(n+1)*a[n+1])/2 for n in range(last)]
    return a, c


def check_constants():
    third = Fraction(1,3)
    log_lower = 2*sum(third**(2*k+1)/(2*k+1) for k in range(3))
    log_upper = 2*third + 2*third**3/3/(1-third**2)
    assert Fraction(693,1000) < log_lower < log_upper < Fraction(7,10)
    e_upper = sum(Fraction(1,factorial(k)) for k in range(5)) + Fraction(1,120)/(1-Fraction(1,6))
    assert e_upper < Fraction(11,4) and Fraction(11,4)**3 < 21

    mu = Fraction(7,20)
    r = 8
    eps = 14*mu**(r+1)
    eps_next = 14*mu**(r+2)
    eta = 196*mu**r
    eta_next = 196*mu**(r+1)
    margin_error = (r+3)*eps + (r+2)*eps_next + eta*(1+eps_next) + eta_next*(1+eps)
    assert margin_error < Fraction(1,10)
    large_a_ratio = (1+14*mu**7)/(Fraction(693,1000)*(1-14*mu**6))
    assert large_a_ratio < Fraction(3,2)
    assert 14*mu**17 < Fraction(1,100)
    assert 196*mu**8 < Fraction(693,1000)
    assert Fraction(9,10)/(4*Fraction(101,100)) > Fraction(1,5)
    assert 5*Fraction(202,100)*Fraction(7,10)**3 < 9
    print('Rational contour comparisons passed.')


def direct_at(j, n, t):
    values = [Fraction(1)]
    for size in range(1, n+1):
        values.append(sum((t if block >= j else 1)*values[size-block]/factorial(block)
                          for block in range(1, size+1)))
    return values


def main():
    check_constants()
    a, c = coefficients(16)
    assert all(a[k+1] <= Fraction(3,2)*a[k] for k in range(6))
    assert all(c[k+1] > Fraction(3,2)*c[k] for k in range(8))
    print('Small unrestricted ratios passed.')
    comparisons = 0
    for j in range(2, 9):
        for old in range(j, 2*j):
            b_old = sum(c[old-size]/factorial(size) for size in range(j, old+1))
            b_next = sum(c[old+1-size]/factorial(size) for size in range(j, old+2))
            x = a[old]/b_old
            value = a[old+1] - x*b_next
            if old+1 == 2*j:
                value += x*x/factorial(j)**2
            actual = direct_at(j, old+1, 1-x)
            assert actual[old] == 0 and actual[old+1] == value < 0
            if old+1 == 2*j:
                print(f'First carry j={j}: {value}')
            else:
                comparisons += 1
    assert comparisons == 28
    print(f'{comparisons} equal-degree signs matched the independent recurrence.')

    j, n, old_root = 3, 3, -12
    actual = direct_at(j, n+1, old_root)
    shifted_profile = [(1 if size < j-1 else old_root)*actual[n-size]/factorial(size)
                       for size in range(n+1)]
    unshifted_profile = [(1 if size < j else old_root)*actual[n-size]/factorial(size)
                         for size in range(n+1)]
    age = Fraction(1,8)
    assert actual[n] == 0
    assert shifted_profile == [0, Fraction(3,2), -6, -2]
    assert unshifted_profile == [0, Fraction(3,2), Fraction(1,2), -2]
    assert sum(coefficient*age**size for size, coefficient in enumerate(shifted_profile)) > 0
    assert sum(coefficient/(size+1) for size, coefficient in enumerate(shifted_profile)) == actual[n+1] == -Fraction(7,4)
    print('Threshold-three age profile has a positive point and integral -7/4.')


if __name__ == '__main__':
    main()
