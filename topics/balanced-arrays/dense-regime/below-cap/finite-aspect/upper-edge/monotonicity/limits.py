from fractions import Fraction as Q
from math import comb, factorial

def interval_sum(base, power_step, first_power, coefficients, terms=12):
    def partial(m):
        return sum(((-1)**j*base**(first_power+power_step*j)/coefficients(j)
                    for j in range(m+1)), Q(0))
    return partial(terms+1), partial(terms)


def pi_interval():
    fragments = [interval_sum(x,2,1,lambda j:2*j+1,14)
                 for x in (Q(1,5),Q(1,239))]
    return (16*fragments[0][0]-4*fragments[1][1],
            16*fragments[0][1]-4*fragments[1][0])


def gaussian_interval(lam):
    low, high = pi_interval()
    root_low, root_high = Q(1253314137,10**9), Q(1253314138,10**9)
    assert 2*root_low**2 < low < high < 2*root_high**2
    num_low, num_high = interval_sum(lam*lam/2,1,0,factorial)
    den_low, den_high = interval_sum(lam,2,1,lambda j:2**j*factorial(j)*(2*j+1))
    h_low, h_high = num_low/(root_high+den_high), num_high/(root_low+den_low)
    alpha = lam+h_low, lam+h_high
    g = 1/alpha[1]-h_high, 1/alpha[0]-h_low
    return alpha,g


def scalar_point(d,r,p):
    w = p/(1-p)
    terms = [comb(d,j)*w**j for j in range(r+1)]
    total = sum(terms)
    t = sum((r-j)*c for j,c in enumerate(terms))/total
    return t, 1/(1+t)-terms[-1]/total


def verify():
    A,B = (scalar_point(80,2,Q(1,p)) for p in (535,555))
    assert A == (Q(153258,82759),Q(6662598651,19532530903))
    assert B == (Q(54846,29533),Q(2549934857,7475895021))
    assert A[0]<B[0] and A[1]>B[1] and B[0]**2 < Q(16,9)*Q(2*78,80)
    print("Fixed-dimension truncated-binomial interval passes")

    A,B = (gaussian_interval(lam) for lam in (Q(23,25),Q(93,100)))
    assert A[0][1]<B[0][0] and B[0][1]<Q(5,4)
    assert A[1][0]>B[1][1] and A[1][0]-B[1][1]>Q(18,10**6)
    print("Gaussian central-cap interval passes below 5/4")


if __name__=="__main__":
    verify()
