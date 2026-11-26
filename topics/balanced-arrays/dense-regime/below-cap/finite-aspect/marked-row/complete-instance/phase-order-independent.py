"""A rational reconstruction of the numerical inequalities in PR #184."""

from fractions import Fraction as Q
from math import factorial

rows, columns, cap = 1_000_000, 250_000, 127_000
start, stop = 507_300, 507_905
residual = rows - 1
small = 7 * residual // 100
large = 8 * residual // 100
maximum_slack = rows * cap - columns * (start - 1)
assert columns * (stop + 1) <= (rows - 2) * cap

# Count 00 singletons in an auxiliary column and potential partners.
mean_occupied = Q(cap * (residual - (stop - 1) - large) - maximum_slack, columns - 2)
assert mean_occupied > large + 1
assert mean_occupied * (mean_occupied - large - 1) >= 3 * (large + 1) ** 2
assert large - small >= 18
inverse_mean_upper = Q(1, small + 1) + Q(1, 2 * 3**18)
assert inverse_mean_upper <= Q(4, columns + 4)

# Use the Taylor lower bound for 1-exp(-x) directly.
x = Q(4 * cap, rows + 1)
chord_lower = Q(columns, cap) * sum(
    (-1) ** (j + 1) * x ** j / factorial(j) for j in range(1, 11)
)
# log(4) = 4 atanh(1/3), with a geometric bound on the remaining positive series.
terms = 12
log4_upper = 4 * (
    sum(Q(1, (2*j + 1) * 3**(2*j + 1)) for j in range(terms))
    + Q(1, (2*terms + 1) * 3**(2*terms + 1)) / (1 - Q(1,9))
)
effective_rank = Q(cap * (columns - cap), columns)
gains = []
for k in range(start, stop + 1):
    slack = rows * cap - columns * (k - 1)
    average = Q(rows * cap - columns * k, rows)
    mixed = Q(slack * (slack - 1), rows * residual)
    correction_a = (mixed+Q(slack, rows))/effective_rank + Q(2*slack, rows*cap)
    correction_b = 2*mixed*(1/effective_rank+Q(1,cap))
    saturated = Q(residual, residual+slack) * (1-min(correction_a, correction_b))
    missing_loss = Q((columns-cap)*rows, columns*(rows-k+1)) * saturated
    gains.append((average*missing_loss, k))
minimum, minimum_index = min(gains)
curvature = Q(4*columns, rows+2) + minimum * chord_lower
assert minimum_index == start
assert minimum > Q(4986304,10**7)
assert curvature > log4_upper
print(f"All {len(gains)} phase-order indices independently pass the curvature gate.")
print(f"Minimum at {minimum_index}; curvature > {curvature.numerator*10**8//curvature.denominator}/10^8 > log 4.")
