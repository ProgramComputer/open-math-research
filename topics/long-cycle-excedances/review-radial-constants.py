"""Independent rational boundary checks for the wider-circle proof."""
from fractions import Fraction as Q
from math import ceil, factorial


def exp_bounds(x, through=72):
    assert 0 <= x < through + 2
    lower = sum(x**j / factorial(j) for j in range(through + 1))
    next_term = x**(through + 1) / factorial(through + 1)
    return lower, lower + next_term / (1 - x / (through + 2))


def log_bounds(x, through=32):
    assert x >= 1
    q = (x - 1) / (x + 1)
    lower = 2 * sum(q**(2*j+1) / (2*j+1) for j in range(through))
    return lower, lower + 2 * q**(2*through+1) / ((2*through+1) * (1-q*q))


pi_lower, pi_upper = Q(157, 50), Q(22, 7)
minimum_k, minimum_n = 400, 10**6
lower_e, upper_e = exp_bounds(Q(1))
assert pi_upper**2 < 10 and pi_upper**2 / 2 < Q(9, 4)**2
assert 3 < Q(9, 4)**2
assert 16 / pi_lower**2 + Q(1, minimum_k) < Q(129, 100)**2
assert 1 / (lower_e * (1 - Q(1, 2 * minimum_k))) < Q(38, 100)
U = Q(129, 100)
small_radius_error = Q(12, minimum_k) + (upper_e + 1)*(2 + Q(9,2)*U) + Q(76,100)*(2 + Q(9,4)*U)
assert small_radius_error < 34

assert pi_upper**2 / 32 < Q(31, 100)
assert Q(31, 100 * minimum_k) < Q(1, 1000)
assert Q(31,100) + Q(1001,1000) < Q(132,100)
assert 2*Q(1001,1000)*Q(5,4)*exp_bounds(Q(33,20))[1] < Q(27,2)
assert Q(1001,1000)*Q(5,4)*exp_bounds(Q(31,80))[1] < 2
assert Q(1,50) - Q(132,100*minimum_k) > Q(1,60)
assert Q(120,minimum_k)*Q(1001,1000) < Q(31,100)
assert exp_bounds(Q(2,3))[1] < 2
assert exp_bounds(Q(6))[0] > 400
assert 7 / exp_bounds(Q(6))[0] < Q(1,10)
assert 2/Q(69,100) < 3
large_radius_error = Q(27,2) + 2 + 2 * (Q(31,100) + Q(1,10) + 3)
assert large_radius_error < 34

assert 1 + exp_bounds(pi_upper)[1] < 25
assert 4*pi_lower**2 / (1+Q(1,minimum_k)+Q(1,40*minimum_k)) > 2
assert Q(17,10)**2 < 3 and Q(17,10)*Q(11,12)/pi_upper > Q(1,4)
assert Q(9,10) - Q(9,10)**2/(2*minimum_k) > Q(89,100)
assert 26*(40+pi_upper**2) < 1300
assert exp_bounds(Q(13))[0] > 130000
assert (16*minimum_k+pi_upper**2)*(Q(2,minimum_k)+Q(1,minimum_k**2)) < 33 < 8*pi_lower**2

assert 1 + pi_upper**2/32 < Q(132,100)
assert 2*pi_lower*(minimum_k-1) > 50**2
assert pi_upper*exp_bounds(Q(132,100))[1]*(Q(1,80)+Q(1,50)) < Q(12,25)
assert Q(2,minimum_k)+Q(1,minimum_k**2) < Q(6,1000)
assert 1/(2*(1+Q(6,1000))) > Q(49,100)
p3_bound = Q(3)/exp_bounds(Q(2))[0]
pole_tail_bound = (5+Q(25,37))/exp_bounds(Q(37,100)*24)[0]
assert p3_bound + pole_tail_bound < Q(21,50)
assert Q(21,50) + Q(2,100) < Q(1,2)

assert Q(7,20) - Q(1,6000) > Q(17,50)
assert Q(7,20) + Q(1,1000) < Q(9,25)
assert Q(9,25)*pi_upper/1000 < Q(1,100)
assert (Q(17,50)*pi_lower*(1-Q(1,60000)))**2 > 1
assert (1-Q(1,20000))/Q(9,25) > 2
assert Q(12,25) + Q(1,100) < pi_lower/6
assert Q(1,3)-1/(36*(350+Q(5,6))) > Q(33,100)
assert Q(33,100)/Q(9,25)**2 > Q(5,2)
assert exp_bounds(Q(5,2))[0] > Q(459,40)

log_two = log_bounds(Q(2))
log_five_over_four = log_bounds(Q(5,4))
log_ten = [3*a+b for a,b in zip(log_two,log_five_over_four)]
log_n_at_min = [6*a for a in log_ten]
short_threshold = [47+Q(5,2)*a for a in log_n_at_min]
largest_k_at_min = int(Q(89*minimum_n,100)/short_threshold[1])
assert Q(89*minimum_n,100*largest_k_at_min) > short_threshold[1]
assert Q(89*minimum_n,100*(largest_k_at_min+1)) < short_threshold[0]
log_250000 = [5*a+b+c for a,b,c in zip(log_ten,log_two,log_five_over_four)]
assert log_250000[1] < Q(25,2)
sqrt_n0 = 250000
assert Q(89*sqrt_n0,100*2000) > 47 + 5*log_250000[1]
assert Q(89,100*2000) > Q(5,sqrt_n0)
assert Q(sqrt_n0**2,200*400) > 20 + 60*log_250000[1]
assert Q(1,200*400) > Q(30,sqrt_n0**2)

print("Taylor contraction errors are below", Q(ceil(small_radius_error*10**6),10**6), "and", large_radius_error)
print("Nonprincipal weighted residue sum is below", Q(ceil((p3_bound+pole_tail_bound)*10**6),10**6))
print("At old size 1,000,000, the revised short-cycle condition holds through threshold", largest_k_at_min)
print("The contour, phase join, and combined cutoff at 250,000^2 pass independently.")
