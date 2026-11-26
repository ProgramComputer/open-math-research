"""Exact weighted hereditary-array example, using direct labeled rows."""
from collections import Counter
from itertools import product

D = 4
FULL = (1 << D)-1
row_options = []
for i in range(D):
    diagonal = 1 << i
    row_options.append([m for m in range(1 << D) if m == diagonal or not m & diagonal])

coefficients = [0]*(D+1)
by_cost = Counter()
by_quota = [[] for _ in coefficients]
for rows in product(*row_options):
    quotas = [sum(bool(m & (1 << j)) for m in rows) for j in range(D)]
    if len(set(quotas)) != 1:
        continue
    k = quotas[0]
    cheap = sum(bool(m & (1 << i)) for i, m in enumerate(rows))
    coefficients[k] += 20**cheap
    by_cost[k, D*k-cheap] += 1
    by_quota[k].append(rows)
assert coefficients == [1, 163121, 321, 1, 0]
assert by_cost == {(0, 0): 1, (1, 0): 1, (1, 2): 6, (1, 3): 32, (1, 4): 81,
                   (2, 7): 12, (2, 8): 81, (3, 12): 1}
minor = coefficients[2]**2 - coefficients[1]*coefficients[3]
assert minor == -60080
assert coefficients[2]**2 - 3*coefficients[1]*coefficients[3] < 0
hits = [sum(tuple(FULL ^ m for m in a) in by_quota[j] for a in by_quota[i])
        for i, j in ((2, 2), (1, 3))]
assert hits == [0, 1]
print(coefficients, minor, "squarefree-union products", hits)
