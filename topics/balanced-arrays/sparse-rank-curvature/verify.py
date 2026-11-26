"""Check a crossover witness using only exact rational arithmetic."""
from fractions import Fraction

r = 2**48
d = r**2
gain = 2**23

# log 4 = 4 atanh(1/3).
terms = 24
log_lower = 4 * sum(
    (Fraction(1, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(terms)),
    Fraction(),
)
log_upper = log_lower + Fraction(
    4, (2 * terms + 1) * 3 ** (2 * terms + 1)
) * Fraction(9, 8)
assert Fraction(4, 3) < log_lower < log_upper < Fraction(3, 2)
assert 24 * log_lower > 32
assert 64 * gain**2 <= r * 24 * log_lower

n = d**2 // ((r - Fraction(gain, 2)) * log_lower)
assert n >= d >= 2 * r
assert r**3 // 2 < n < d**2
new_step = Fraction(d, d + n * (r - gain))
old_step = Fraction(d, d + n * (r - 1))
assert d * (new_step - new_step**2 / 2) > log_upper
assert d * old_step < log_lower

degree = n * r // d
k = degree - 1
assert k >= 1
# Upper bound for the log curvature of the unrestricted binomial coefficients.
assert d * (Fraction(1, k) + Fraction(1, n - k)) < log_lower
print(f"r={r}, d={d}, n={n}, degree={degree}, conservative gain={gain}")
print("New criterion passes. Earlier r-1 criterion and unrestricted test at D-1 fail.")
