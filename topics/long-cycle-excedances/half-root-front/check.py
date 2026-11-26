"""Exact scalar inequalities for the half-square-root exterior theorem."""
from fractions import Fraction as Q
from math import factorial


def exp_lower(x, terms=48):
    return sum((x**j / factorial(j) for j in range(terms+1)), Q(0))


def exp_upper(x, terms=48):
    return exp_lower(x,terms)+x**(terms+1)/factorial(terms+1)/(1-x/(terms+2))


def verify():
    # Boundary probability E. Multiply by v^3 to cover the uses of p E/alpha.
    v=1000
    assert 4*v**3*factorial(8)/(Q(4,5)*v)**8 < Q(1,1000)
    # At p in [.30,.60] sqrt(n) the two color-size deviations cost little.
    l=1/exp_lower(Q(125,21))
    lstep=1/exp_lower(Q(250,21))
    assert 2*l/(1-lstep)+Q(1,1000)<Q(1,100)
    u=1/exp_lower(Q(125,18))
    ustep=1/exp_lower(Q(125,9))
    assert 2*u*(Q(3,2)/(1-ustep)+ustep/(1-ustep)**2)<Q(1,100)
    # Ratio and one-sided color insertion estimates.
    assert Q(101,99)*Q(8,5)*2<Q(10,3)
    assert Q(10,3)*(1+Q(1,300))<Q(17,5)
    assert Q(1001,990)*2*(Q(1,20)+Q(1,300))<Q(1,8)
    assert Q(100,99)*(2*Q(501,1000)/20+Q(2,1000)) < Q(1,18)
    # Short-cycle lag in the comparison between n and n+1, from beta masses.
    assert sum((-1)**(j-1)*Q(1,2)**j/j for j in range(1,7)) > Q(2,5)
    k=10000
    assert 10000*k*k*factorial(8)/(Q(k,15))**8<Q(1,2)
    assert exp_upper(Q(1,12*10**6))**2 < 2*3*(1-Q(1,k))*Q(19,20)
    assert Q(3,5)**2/20 < Q(7,50)**2
    assert Q(100,99)*(Q(16,3)+Q(16,9)) < Q(15,2)
    assert Q(15,2)*Q(57,50)/100+Q(2,1000)<Q(1,10)
    assert (100*k)**2 * factorial(6)/k**6 < Q(1,1000)

    # Dominant two adjacent monomials, and normalized local tail bounds.
    q=Q(19,1000)
    left_inv,right=Q(9,8),Q(17,5)
    assert exp_lower(1/Q(501,1000)**2)>1/q
    assert 2*q*left_inv<Q(1,5) and 3*q*right<Q(1,5)
    assert (25*41)**3*Q(1,5)**40<Q(1,1000)
    assert Q(42,41)**3<5

    def tails(low,high):
        s=q*left_inv/low
        u=q*right*left_inv*high
        left=Q(10,3)*(s/(1-s)+s/(300*(1-s)**2))
        right_tail=high*u/(1-u)
        return left+right_tail

    assert tails(Q(3,4), Q(5,4))+Q(1,1000)<Q(1,4)
    assert tails(Q(1,2), Q(1,2))+Q(1,1000)<Q(1,2)
    assert tails(Q(3),Q(3))+Q(1,1000)<2
    s=q*left_inv/Q(3,4)
    u=q*right*left_inv*Q(5,4)
    weighted_left=Q(10,3)*(s/(1-s)**2+s*(1+s)/(300*(1-s)**3))
    weighted_right=Q(5,4)*(1/(1-u)**2-1)
    # The local coefficient-change term has |p(delta alpha)|/alpha<1/10.
    assert weighted_left+weighted_right+Q(1,1000)+Q(1,10)*(1+Q(5,4)+Q(1,4))<Q(3,4)

    # The first middle sample succeeds the largest of the front brackets.
    assert 1/(2*Q(501,1000)**2)>Q(3,2)
    assert exp_lower(Q(3,2))>Q(17,4)
    assert Q(157,50)**2/4*(1-Q(22,7)**2/(24*10**6))**2>Q(49,20)
    print("All exact constants pass for the half-square-root exterior range.")

if __name__=="__main__":
    verify()
