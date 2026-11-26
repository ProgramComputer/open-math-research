"""Rational constants for the comparable row-slices argument, stated in phase-order.md."""
from fractions import Fraction as Q
from math import factorial

N, D, R = 10**6, 250000, 127000
FIRST, LAST = 507300, 507905


def verify_switches():
    height = N-1
    kappa_max = LAST-1
    early, late = 7*height//100, 8*height//100
    free_cells = N*R-D*(FIRST-1)
    assert D*(LAST+1) <= (N-2)*R
    mean_b = Q(R*(height-kappa_max-late)-free_cells,D-2)
    assert mean_b>late+1
    assert mean_b*(mean_b-late-1) >= 3*(late+1)**2
    assert late-early>=18
    absent = Q(1,early+1)+Q(1,2*3**18)
    assert absent<1
    assert 1/(1-absent) <= 1+Q(4,D)
    print('Every marked-column swap obeys the bound needed for both nested slice couplings.')


def loss_times_deficit(k):
    quota = k-1
    s = N*R-D*quota
    t = Q(N*R-D*k,N)
    effective_rank = Q(R*(D-R),D)
    first = (Q(s*(s-1),N*(N-1))/effective_rank + Q(s,N)/effective_rank
             + Q(2*s,N*R))
    second = (2/effective_rank+Q(2,R))*Q(s*(s-1),N*(N-1))
    correction = min(first,second)
    alpha = Q((D-R)*N,D*(N-quota))
    return alpha*t*Q(N-1,N+s-1)*(1-correction)


def main():
    verify_switches()
    delta_r = Q(4*R,N+1)
    exp_lower = sum(delta_r**j/factorial(j) for j in range(9))
    chord = Q(D,R)*(1-1/exp_lower)
    scores = [(loss_times_deficit(k),k) for k in range(FIRST,LAST+1)]
    minimum,k = min(scores)
    lower = Q(4*D,N+2)+minimum*chord
    assert chord>Q(39,50) and minimum>Q(496,1000)
    assert sum(lower**j/factorial(j) for j in range(12))>4
    print(f'{len(scores)} exact curvature checks cover {FIRST}..{LAST}.')
    print(f'Minimum certified loss times deficit at {k}: greater than {int(minimum*10**7)}/10^7.')
    print(f'Uniform log curvature exceeds {int(lower*10**8)}/10^8 and the quotient exceeds four.')


if __name__=='__main__':
    main()
