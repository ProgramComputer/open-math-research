"""Count rank-two arrays through matchings of distinct column stubs."""
from fractions import Fraction as Q


def complete_matchings(size):
    a = [1]
    for h in range(size//2):
        a.append(a[-1]*(size-2*h)*(size-2*h-1)//(2*(h+1)))
    return a


def multiply(a,b):
    p = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            p[i+j] += x*y
    return p


def expectation(n, quotas):
    cells = sum(quotas)
    rook = [1]
    for k in quotas:
        rook = multiply(rook,complete_matchings(k))
    allowed = [0]*(cells//2+1)
    for i, count in enumerate(rook):
        mul = (-1)**i*count
        for j, factor in enumerate(complete_matchings(cells-2*i)):
            allowed[i+j] += mul*factor
    fall = [1]
    for j in range(min(n,cells)):
        fall.append(fall[-1]*(n-j))
    total, numerator = 0,0
    for h,m in enumerate(allowed):
        assert m >= 0
        if cells-h > n:
            continue
        weight = m*fall[cells-h]
        total += weight
        numerator += weight*(n-h)
    return Q(numerator,total)


def error(n, quotas):
    slack = 2*n-sum(quotas)
    return expectation(n,quotas)-(Q(n*slack,n+slack-1) if slack else Q(0))
