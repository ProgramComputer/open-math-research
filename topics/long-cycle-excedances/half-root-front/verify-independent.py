"""Independent scalar reconstruction for the half-square-root front and middle."""
from fractions import Fraction as Q
from math import factorial


def exp_lower(x):
    return sum((x**n / factorial(n) for n in range(61)), Q(0))


def log_lower(x):
    t = (x-1)/(x+1)
    return 2*sum((t**(2*j+1)/(2*j+1) for j in range(25)), Q(0))


def upper_dyadic(x, bits=64):
    grid = 1 << bits
    return Q((x*grid).__ceil__(), grid)


v = 1000
k = 10_000
assert Q(5,6)*(1-Q(1,v*v)) > Q(4,5)
boundary = Q(4*v**3*factorial(8),1) / (Q(4,5)*v)**8
assert boundary < Q(1,1000)
a_down = 1/exp_lower(Q(125,21))
step_down = 1/exp_lower(Q(250,21))
a_up = 1/exp_lower(Q(125,18))
step_up = 1/exp_lower(Q(125,9))
assert 2*a_down/(1-step_down) + boundary < Q(1,100)
assert a_up*(3/(1-step_up) + 2*step_up/(1-step_up)**2) < Q(1,100)
assert Q(202,99)*Q(8,5)<Q(10,3)
assert (1+boundary)*Q(200,99)*(Q(1,20)+Q(1,300)) < Q(1,8)
assert (2*Q(501,1000)/20+Q(2,v))/Q(99,100) < Q(1,18)
assert log_lower(Q(3,2))-Q(1,3)>Q(1,15)
assert Q((100*k)**2*factorial(8),1)/(Q(k,15)**8)<Q(1,2)
assert Q((100*k)**2*factorial(6), k**6)<Q(1,1000)
assert Q(1,6)*Q(k,k-1)*Q(20,19)*2<1  # e^(1/(6n)) < 2
assert Q(3,5)**2/20 < Q(7,50)**2
residual_relative = Q(16,3)*Q(100,99)*Q(4,3)
assert residual_relative < Q(15,2)
assert Q(15,2)*Q(57,50)/100 + Q(2,1000) < Q(1,10)

q = Q(19,1000)
assert exp_lower(1/Q(501,1000)**2) > 1/q
assert 2*q*Q(9,8) < Q(1,5)
assert 3*q*Q(17,5) < Q(1,5)
assert Q((25*41)**3,5**40) < Q(1,1000)
assert Q(42,41)**3 < 5


def pair_tails(radius_min, radius_max, weighted):
    """Sum the two local, outward geometric tails."""
    x = q * Q(9,8) / radius_min
    y = q * Q(17,5) * Q(9,8) * radius_max
    left = x/(1-x)
    left_first = x/(1-x)**2
    left_second = x*(1+x)/(1-x)**3
    right = y/(1-y)
    right_first = y/(1-y)**2
    if weighted:
        return Q(10,3)*(left_first+left_second/300) + radius_max*(right+right_first)
    return Q(10,3)*(left+left_first/300) + radius_max*right


for lower, upper, goal in (
    (Q(3,4),Q(5,4),Q(1,4)),
    (Q(1,2),Q(1,2),Q(1,2)),
    (Q(3),Q(3),Q(2)),
):
    assert pair_tails(lower,upper,False)+Q(1,1000) < goal
sign_error = pair_tails(Q(3,4),Q(5,4),True)+Q(1,1000)+Q(1,4)
assert sign_error < Q(3,4)
assert 1/(2*Q(501,1000)**2)>Q(3,2)
assert exp_lower(Q(3,2))>Q(17,4)
assert Q(157,100)**2*(1-Q(22,7)**2/(24*10**6))**2>Q(49,20)


def moments(coefficient):
    end = 101
    indices = range(-end,end+1,2)
    weights = {p: upper_dyadic((1+coefficient*(p*p-1))**(-96)) for p in indices}
    assert 191*coefficient*end**2 > 1-coefficient
    first_tail = upper_dyadic(1/((1+coefficient*(end*end-1))**95*190*coefficient))
    zero_tail = first_tail / end
    mass = sum(weights.values())+zero_tail
    first = sum(abs(p)*w for p,w in weights.items())+first_tail
    uniform = max(
        sum(w/abs(a-p) for p,w in weights.items() if p != a)
        for a in range(-end-2,end+3,2)
    ) + zero_tail/2
    return mass, first, uniform


def degree_split_margin(lo, hi, threshold):
    W, W1, U = moments(Q(999,1000)*Q(49,20)/(192*hi))
    V, V1, _ = moments(Q(49,20)*(1-Q(1,lo))/384)
    derivative_factor = Q(1,lo*threshold)
    tiny = 1/exp_lower(Q(lo-1,8))
    short_factor = 2*U/threshold
    long_factor = 5*U/threshold
    assert long_factor<1
    short_sum = short_factor/(1-short_factor)
    long_sum = long_factor/(1-long_factor)
    bound_v = V*short_sum+tiny*W*long_sum
    bound_d = (
        V1*short_sum + tiny*W1*long_sum
        + derivative_factor * (6*(V*W+V1*U)+short_factor*V)/(1-short_factor)
        + tiny*derivative_factor * (11*(W*W+W1*U)+long_factor*W)/(1-long_factor)
    )
    bound_lag = W*(V+bound_v)*derivative_factor
    return 1-(bound_v+Q(1,50))**2-(bound_d+bound_lag+Q(1,16)+Q(1,100))**2


def floor_million(x):
    return (10**6*x).__floor__()


print(f"Exterior actual-next error < {floor_million(sign_error)+1}/10^6 in normalized units.")
for lo,hi,A in (
    (20,25,24),(25,32,21),(32,40,18),(40,50,17),(50,64,16),
    (64,80,16),(80,92,16),(92,96,16),(96,100,17),
):
    slack = degree_split_margin(lo,hi,A)
    assert slack>0
    cut = max(10**6, 1000*hi, Q(20*(hi*A)**2,49).__ceil__())
    assert cut == (10**6 if hi<=96 else 1_179_592)
    print(f"{lo}..{hi}, A={A}: squared sign slack > {floor_million(slack)}/10^6, old row cutoff {cut:,}.")
assert Q(89,100)*96 > 47+Q(5,2)*Q(153,10)
assert exp_lower(Q(153,10)) > 4_062_720
