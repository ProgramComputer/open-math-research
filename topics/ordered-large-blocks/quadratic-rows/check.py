from fractions import Fraction
from math import comb, factorial


MAX_THRESHOLD = 63
FACTORIALS = [factorial(n) for n in range(3*MAX_THRESHOLD+1)]
WEIGHTS = [Fraction(1, f) for f in FACTORIALS]


def unrestricted(last):
    a = [Fraction(1)]
    for n in range(1, last+1):
        a.append(sum(WEIGHTS[size]*a[n-size] for size in range(1, n+1)))
    c = [(a[n]+(n+1)*a[n+1])/2 for n in range(last)]
    triple = [sum(a[i]*c[n-i] for i in range(n+1))
              for n in range(MAX_THRESHOLD+1)]
    return a, c, triple


def constants(triple):
    low, high = Fraction(693147, 10**6), Fraction(693148, 10**6)
    third = Fraction(1,3)
    lower_sum = 2*sum(third**(2*j+1)/(2*j+1) for j in range(8))
    upper_sum = lower_sum + 2*third**17/(17*(1-third**2))
    assert low < lower_sum < upper_sum < high
    e_upper = sum(WEIGHTS[k] for k in range(5)) + WEIGHTS[5]/(1-Fraction(1,6))
    assert e_upper < Fraction(11,4) and Fraction(11,4)**3 < 21
    lo = [8*low**(r+3)*triple[r] for r in range(9)]
    hi = [8*high**(r+3)*triple[r] for r in range(9)]
    for r in range(8):
        assert hi[r] < Fraction((r+4)**2, 2)
        assert lo[r+1]-hi[r] > r+2
        assert hi[r+1]-lo[r] < r+4

    mu, gamma = Fraction(7,20), Fraction(1,30)
    assert 2200*(1+mu)*mu**8 < Fraction(19,20)
    assert 2200*mu**8 < 1
    assert 196*mu**20 < Fraction(1,20)
    assert 14*mu**40 < Fraction(1,100)
    assert 14*(1+mu)/(1-14*mu**40) < 30
    assert 196*(1+mu)*mu**20/(1-gamma/mu)+3*gamma**21/(1-gamma) < Fraction(1,100)
    assert 30*mu**40*(40+198) < Fraction(1,100)
    assert 15*mu**40*24**2 < Fraction(1,4)
    assert 6*gamma/(1-gamma)**2 < Fraction(1,4)
    assert 3*Fraction(32,8)-Fraction(451,40) > 0
    assert Fraction(3,8)-Fraction(451,40*64) > Fraction(1,6)
    assert Fraction(1,3)*Fraction(64,67)**2 > Fraction(1,4)
    assert 2*(2+Fraction(198,64))/Fraction(63,64)**2 < 11
    assert 16*11**2/(1-gamma) < 64**2
    print('Exact logarithm bounds, eight low-index triple-pole bounds and rational margins passed.')


def labeled_rows(j, maximum):
    rows = [[1]]
    for n in range(1, maximum+1):
        row = [0]*(1+n//j)
        for size in range(1,n+1):
            weight = comb(n,size)
            mark = int(size>=j)
            for k, value in enumerate(rows[n-size]):
                row[k+mark] += weight*value
        rows.append(row)
    return rows


def moments(j, n, a, c, triple, double_block):
    first = sum(WEIGHTS[size]*c[n-size] for size in range(j,n+1))
    second = sum(double_block[i]*triple[n-2*j-i] for i in range(n-2*j+1))
    third = WEIGHTS[j]**3 if n==3*j else Fraction(0)
    return a[n], first, second, third


def assert_original(n, row, moment):
    formed = [sum((-1)**(h-k)*comb(h,k)*moment[h] for h in range(k,4))
              for k in range(len(row))]
    assert [FACTORIALS[n]*v for v in formed] == row


def check_pairs(a, c, triple):
    equal_degree = carries = 0
    for j in range(2,MAX_THRESHOLD+1):
        rows = labeled_rows(j,3*j)
        double_block = [sum(WEIGHTS[j+i]*WEIGHTS[j+s-i] for i in range(s+1))
                        for s in range(j+1)]
        start = 2*j if j<32 else 3*j-1
        for n in range(start,3*j):
            old = moments(j,n,a,c,triple,double_block)
            new = moments(j,n+1,a,c,triple,double_block)
            assert_original(n,rows[n],old)
            assert_original(n+1,rows[n+1],new)
            av,bv,dv,zero = old
            an,bn,dn,en = new
            assert zero==0 and dv>0
            if en==0:
                scale = an/av
                delta_b = bn-scale*bv
                delta_d = dn-scale*dv
                assert delta_b>0 and delta_d>0
                cut = delta_b/delta_d
                equal_degree += 1
            else:
                # Reduce the next cubic modulo the old quadratic in x=1-t.
                remainder_constant = an-dn*av/dv+en*av*bv/dv**2
                remainder_linear = -bn+dn*bv/dv-en*(bv**2/dv**2-av/dv)
                assert remainder_linear>0
                cut = -remainder_constant/remainder_linear
                carries += 1
            assert av-bv*cut+dv*cut**2<0
    assert (equal_degree,carries)==(465,62)
    print(f'{equal_degree} same-degree pairs and {carries} cubic carries passed exact sign and coefficient checks.')


if __name__ == '__main__':
    a, c, triple = unrestricted(3*MAX_THRESHOLD)
    constants(triple)
    check_pairs(a,c,triple)
