"""Independent boundary checks for the bounded-aspect occupied-pole estimates."""
from fractions import Fraction as Q
from math import ceil, factorial, lcm

TABLE = (
    (4, 5, 17, 10000), (5, 6, 20, 12000), (6, 7, 23, 21601),
    (7, 8, 26, 36054), (8, 9, 29, 56768), (9, 10, 32, 85334),
    (10, 12, 39, 182520), (12, 15, 49, 450188), (15, 20, 66, 1452000),
    (20, 25, 83, 3588021), (25, 32, 108, 9953280), (32, 40, 138, 25392000),
    (40, 50, 175, 63802084), (50, 64, 230, 180565334),
    (64, 80, 294, 460992000), (80, 100, 375, 1171875000),
    (100, 125, 480, 3000000000),
)
SCALE = 1 << 100


def lattice(c):
    # Keep a wider lattice and dominate the remainder by the pure power c^-96 p^-192.
    limit = 1
    while c*limit**2 < 4:
        limit += 2
    p = tuple(range(-limit,limit+1,2))
    w = {a: ceil(SCALE / (1+c*(a*a-1))**96) for a in p}
    t, t1 = [2*c**(-96)*Q(limit)**(r-191)/(191-r) for r in (0,1)]
    W = Q(sum(w.values()),SCALE)+t
    W1 = Q(sum(abs(a)*w[a] for a in p),SCALE)+t1
    den = lcm(*range(2,2*limit+3,2))
    inv = {distance:den//distance for distance in range(2,2*limit+3,2)}
    U = Q(max(sum(w[b]*inv[abs(a-b)] for b in p if a!=b)
              for a in (*p,limit+2)),SCALE*den)+t/2
    # Pair a<b once and restore the two orientations in closed form.
    ta, ea, ja = 0, 0, 0
    for i,a in enumerate(p):
        for b in p[i+1:]:
            weight = w[a]*w[b]*inv[b-a]
            ta += 2*weight
            ea += 2*max(abs(a),abs(b))*weight
            ja += (abs(a)+abs(b))*weight
    pair_den = SCALE**2*den
    big_tail = t1*W+t*W1
    return W,W1,U,Q(ta,pair_den)+t*W,Q(ea,pair_den)+big_tail,Q(ja,pair_den)+big_tail


W, W1, *_ = lattice(Q(1,160))
assert W-2 < Q(1,50) and W1-2 < Q(1,16)

min_slack = None
for low, cap, A, cutoff in TABLE:
    W,W1,U,T,E,J1 = lattice(Q(999,160000*cap))
    alpha = Q(2,A)
    y = alpha*U
    assert y<1
    e1,e2 = y/(1-y),y*y/(2*(1-y))
    v = alpha*T + W*e2
    t = Q(1,low*A)
    j = alpha*(E+t*T) + W1*e2 + alpha*(J1+t*T)*e1
    insertion = t*W*(W+v)
    slack = 1-(v+Q(1,50))**2-(j+insertion+Q(1,16)+Q(1,100))**2
    assert slack>0 and cutoff==max(10000,1000*cap,ceil(Q(5,6)*(cap*A)**2))
    if min_slack is None or slack<min_slack[0]:
        min_slack = (slack,low,cap)
    print(f'{low}..{cap}: A={A}, cutoff={cutoff}, squared slack > {int(slack*10**6)}/10^6')

assert max(row[3] for row in TABLE)==3_000_000_000
assert sum(Q(25,2)**j/factorial(j) for j in range(80))>250000
assert Q(89,100)*125>47+Q(5,2)*25
assert Q(3_000_000_000,200*400)>20+30*25
print(f'Least squared slack occurs in {min_slack[1]}..{min_slack[2]}.')
print('All slab cutoffs, both outer aspect splits and the combined cutoff passed.')
