from fractions import Fraction
from math import comb
from collections import Counter

MAXIMUM = 192
choose = [[comb(n, k) for k in range(n + 1)] for n in range(MAXIMUM + 1)]
stirling = [[1]]
for n in range(1, MAXIMUM + 1):
    previous = stirling[-1]
    stirling.append([0] + [previous[k - 1] + (k * previous[k] if k < n else 0)
                           for k in range(1, n + 1)])
factorial = [1]
for n in range(1, MAXIMUM + 4):
    factorial.append(n * factorial[-1])
# For p ordered gaps and h ordinary unordered blocks there are
# h! * binom(h+p-1,p-1) arrangements of those blocks across the gaps.
gap_counts = [[sum(stirling[n][h] * factorial[h] * comb(h + p - 1, p - 1)
                   for h in range(n + 1)) for n in range(MAXIMUM + 1)]
              for p in range(1, 5)]

def row(n, j):
    moments = [gap_counts[0][n]]
    if n >= j:
        moments.append(sum(choose[n][a] * gap_counts[1][n-a]
                           for a in range(j, n+1)))
    if n >= 2*j:
        moments.append(sum(choose[n][a] * choose[n-a][b] * gap_counts[2][n-a-b]
                           for a in range(j, n-j+1) for b in range(j, n-a+1)))
    if n >= 3*j:
        assert n == 3*j
        moments.append(choose[n][j] * choose[n-j][j])
    # Every partition with H large blocks contributes binom(H,k) times
    # when a subset of k distinguished blocks is selected.
    return [sum((-1)**(k-h) * choose[k][h] * moments[k]
                for k in range(h, len(moments))) for h in range(len(moments))]

def sign(x):
    return (x > 0) - (x < 0)

def radical_sign(a, b, d):
    if not a or not b or sign(a) == sign(b):
        return sign(a) or sign(b)
    return sign(a) * sign(a*a - b*b*d)

def certify(old, new):
    assert all(x > 0 for x in old + new)
    c, b = old[:2]
    if len(old) == 2:
        value = sum(coefficient * (-c)**k * b**(len(new)-1-k)
                    for k, coefficient in enumerate(new))
        assert value < 0
        return
    a = old[2]
    discriminant = b*b-4*a*c
    assert discriminant > 0
    # Evaluate directly in Q(sqrt(discriminant)) by Horner and compare
    # the two signed squares if terms of opposite signs remain.
    for side in (-1, 1):
        u = v = Fraction(0)
        for coefficient in reversed(new):
            u, v = (coefficient + (-b*u + side*discriminant*v)/(2*a),
                    (side*u - b*v)/(2*a))
        assert radical_sign(u, v, discriminant) == -side

assert [row(n, 3) for n in range(1, 7)] == [
    [1], [3], [12, 1], [66, 9], [450, 91], [3690, 973, 20]]
counts = Counter()
for j in range(2, 65):
    # Include the first analytic cutoff in each band as a cross-check.
    for n in range(j, 3*j):
        if ((j <= 9 and n < 2*j) or
                (j <= 32 and 2*j <= n < 3*j-1) or
                (2*j <= n == 3*j-1)):
            old, new = row(n, j), row(n+1, j)
            certify(old, new)
            counts[(len(old)-1, len(new)-1)] += 1
print(sorted(counts.items()))
