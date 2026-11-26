"""Independent exact scalar reconstruction for the wide differentiated slab."""
from fractions import Fraction
from math import factorial

Q = Fraction


def exp_enclosure(value):
    """Positive Taylor interval at x/32, raised to the 32nd power."""
    assert 0 <= value <= 32
    x = value / 32
    term = lower = Q(1)
    for j in range(1, 21):
        term *= x / j
        lower += term
    upper = lower + term * x / 21 / (1 - x / 22)
    return lower**32, upper**32


def arctan_enclosure(x):
    first = sum(((-1)**j * x**(2*j+1) / (2*j+1)
                 for j in range(24)), Q(0))
    return first, first + x**49 / 49


def show(name, value, places=9):
    scale = 10**places
    outward = (value.numerator * scale + value.denominator - 1) // value.denominator
    print(f"{name} < {outward // scale}.{outward % scale:0{places}d}")


atan5 = arctan_enclosure(Q(1, 5))
atan239 = arctan_enclosure(Q(1, 239))
pi_lo = 16 * atan5[0] - 4 * atan239[1]
pi_hi = 16 * atan5[1] - 4 * atan239[0]
assert Q(157,50) < pi_lo < pi_hi < Q(22,7)
# Keep ordinary simple inputs for bounding the remaining exponentials.
pi_ceiling = Q(22, 7)
pi_floor = Q(157, 50)
cycle, ratio = 225, 49
angle_sq = Q(1, 25 * cycle)
load = Q(6, 5) * Q(49, 50)
assert Q(1, 50) / (1 - angle_sq) < Q(1, 49)
assert Q(999,1000)**2 < 1 - angle_sq
assert Q(1,50) - Q(1,50)**3 / 6 > Q(1,75)

a = exp_enclosure(Q(13, 25) + Q(1, 49))[1]
block_first = Q(1, 2) + Q(1, 4 * cycle)
# k times the zeroth-moment bound, and the actual first-moment bound.
moment0 = a + block_first*a**2
moment1 = a + 2*block_first*a**2
for block in range(2, 24):
    bound = a**(block+1) / (2 * factorial(block))
    moment0 += bound
    moment1 += (block+1)*bound
first_remainder = a**25 / (2 * factorial(24))
moment0 += first_remainder / (1 - a/25)
moment1 += 25 * first_remainder / (1 - 2*a/25)
assert moment0 < 6 and moment1 < 15 and moment0*moment1 < 100
assert Q(1, 2*factorial(16)) / (1 - Q(1,17)) < Q(1,10**12)

value_weight = Q(6000)
derivative_weight = Q(21000)
assert 4 * exp_enclosure(pi_ceiling + 4)[1] < value_weight
j_bound = Q(15, ratio*cycle) + Q(10, 15) / load + Q(6, cycle) / load
assert value_weight * (pi_ceiling/2 + 4) * j_bound < derivative_weight
e_min = exp_enclosure(Q(1))[0]
assert Q(16, ratio) + Q(25, ratio) / e_min < Q(53,100)
assert exp_enclosure(Q(13,25)*(ratio-16))[0] > 20_000_000
assert exp_enclosure(Q(13,25)*(ratio-1))[0] > 25_000_000_000

# Independently include four initial pairs before starting the odd-lattice integral.
beta = load / 192
assert 191 * beta * 7**2 > 1-beta
odd_far_bound = sum((2 * p / (1 + beta*(p*p-1))**96 for p in (7,9,11,13)), Q(0))
odd_far_bound += 1 / (2*beta*95 * (1 + beta*(13**2-1))**95)
assert odd_far_bound < Q(1,10**8)
assert (Q(13,25) * ratio > 1)  # exponential beats X and sqrt(X)
# Uniform pole mass follows directly from 2+2/sqrt(load/X); the first moment
# follows from 2+2/sqrt(load/X)+3X/load. Compare using X >= 1.
assert load > 1
assert 2 + 2 < Q(9,2)
assert 2 + 2 + 3/load < Q(33,4)
# At box face X=49, these are the two pole maxima used in the fast group.
mass_fast = Q(9,2) * 7
moment_fast = Q(33,4) * 49
short_scalar = Q(1,10**12)
long_scalar = Q(1,20_000_000)
fast_scalar = Q(1,25_000_000_000)
value_error = (
    6*value_weight*(short_scalar + long_scalar)
    + value_weight*odd_far_bound
    + value_weight*mass_fast*fast_scalar
)
derivative_error = (
    (18*value_weight + 6*derivative_weight)*short_scalar
    + (18*value_weight*Q(53,100) + 6*derivative_weight)*long_scalar
    + (value_weight + derivative_weight)*odd_far_bound
    + (value_weight*moment_fast + derivative_weight*mass_fast)*fast_scalar
)
assert value_error < Q(1,500)
assert derivative_error < Q(1,100)

assert 5*pi_floor*Q(999,1000) > 15
assert Q(12,25) + Q(1,49) < Q(51,100)
assert 2*pi_floor*224 > 37**2
h_derivative = pi_ceiling*Q(5,3)*(Q(1,225) + Q(1,37))
assert exp_enclosure(Q(51,100))[1] < Q(5,3)
assert h_derivative < Q(17,100)
assert Q(1,147) + Q(17,100) / load < Q(16,100)
assert exp_enclosure(Q(225,18))[0] > 101
assert exp_enclosure(Q(59,50))[1] < Q(10,3)
assert Q(9,10) / (pi_ceiling + Q(9,2)/Q(999,1000)) > Q(23,200)
other = {}
for p, claimed in [(3, Q(1,50)), (5, Q(1,100_000))]:
    log_damping = load*(p*p-1) / (2*(1+(p*p-1)*angle_sq))
    assert exp_enclosure(log_damping - Q(17,100)*(p+1))[0] > 1/claimed
    other[p] = claimed
near_nonprincipal = sum(other.values())
near_nonprincipal_derivative = sum(
    (p + Q(16,100))*mass for p, mass in other.items()
)
value_total = value_error / Q(23,100) + near_nonprincipal
assert value_total < Q(3,100)
assert 1 - value_total**2 > Q(99,100)**2
assert 1-Q(19,100)**2/2 > value_total
correction = Q(16,100) + near_nonprincipal_derivative + derivative_error / Q(23,100)
assert Q(99,100) - correction > Q(71,100)
assert Q(4,50) < Q(29,100)**2
assert ((1+value_total) * (Q(2,50)+Q(29,100))/3) < Q(12,100)

start = 1_408_334
previous = 4_062_720
assert Q(6,5)*start > (3*96)**2
assert start > 25*(24**2)*96
assert start >= 1000*96
assert (Q(5,6)*(50*26)**2).__ceil__() == start
assert Q(89,100)*96 > 47 + Q(5,2)*Q(153,10)
assert exp_enclosure(Q(153,10))[0] > previous
show("k times coefficient error", value_error)
show("k times normalized coefficient derivative error", derivative_error)
show("Relative old value error", value_total)
show("Total normalized old derivative correction", correction)
print(f"Both insertion signs verified under the slab hypotheses. Crossover starts at {start:,}.")
