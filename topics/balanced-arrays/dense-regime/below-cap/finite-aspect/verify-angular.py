from fractions import Fraction as Q
from math import factorial


def exp_lower(x, terms):
    return sum((x**j / factorial(j) for j in range(terms + 1)), Q(0))


def main():
    n = 10**6
    d = n // 4
    eta = Q(1, 10**6)
    p = Q(1, 2) + Q(3, n)
    cap = Q(127000, d)
    s = exp_lower
    checks = {
        "inside phase bracket": Q(1,4)+Q(100,n)+Q(1,10**4) < 1,
        "phase bracket margin": Q(300,n)+Q(3,10**4) > Q(33,n)+Q(1,10**4),
        "logit error budget": 6*101+25 < 650,
        "log amplitude budget": Q(2350,3*n)+Q(6,10**4)+2*eta < Q(2,1000),
        "six term error": 1/(1-Q(2,1000)) < Q(1003,1000),
        "uniform derivative at cosine": s(Q(3,2),5) > Q(40,9) and s(Q(4),4) > 30,
        "centered ideal": 1-2*Q(607,1000)+2*Q(135,1000)-2*Q(12,1000) == Q(32,1000),
        "last term ratio": s(Q(2496,1000),5) > Q(100,9),
        "last term magnitude": Q(12,1000)*Q(1003,1000) < Q(13,1000),
        "absolute tails": 2*Q(13,1000)*Q(9,100)/(1-Q(9,100)) < Q(3,1000),
        "angular projection": Q(32,1000)-6*Q(3,1000)-Q(3,1000) > Q(1,100),
        "rational unrestricted log error": Q(400+3*4,3*n) < Q(1,1000),
        "rational validity multiplication": Q(99,100)*(1-Q(1,1000)) > Q(989,1000),
        "rational exponential upper error": 1/(1-Q(1,1000)) < Q(1002,1000),
        "rational ideal mass": s(Q(2),7) > Q(125,17) and 1+2*(Q(607,1000)+Q(136,1000)+Q(12,1000)) == Q(251,100),
        "rational projection": Q(32,1000)-Q(251,100)*Q(11,1000)-Q(3,1000) > Q(1,1000),
        "example Hoeffding exponent": 2*d*(cap-p)**2 > 30,
        "exact exp 30 witness": s(Q(5),6) > 100,
        "symmetric first ratio exponent": Q(n,2*n+4) > Q(49,100),
        "symmetric curvature": Q(n,n+2) > Q(49,50),
        "symmetric local error": Q(304,4*n) < Q(1,10000),
        "symmetric absolute correction": 1/(1-Q(1,10000)) < 1+Q(2,10000),
        "symmetric lower seven terms": Q(32,1000)-6*Q(2,10000) > Q(30,1000),
        "symmetric exponential bounds": s(Q(49,100),3) > Q(50,31) and s(Q(49,25),4) > Q(25,4) and s(Q(49,20),5) > 10,
        "symmetric positive mass": 1+2*(Q(31,50)+Q(4,25)/(1-Q(1,10))) < 3,
        "symmetric tail exponents": Q(49,100)*36 > 17 and Q(49,100)*13 > 1 and Q(8,3)**17 > 10**7,
        "symmetric perturbation": 3*eta+Q(4,10**7) < Q(4,10**6) < Q(1,100),
    }
    for name, result in checks.items():
        assert result, name
    print(f"{len(checks)} exact rational checks passed")


if __name__ == "__main__":
    main()
