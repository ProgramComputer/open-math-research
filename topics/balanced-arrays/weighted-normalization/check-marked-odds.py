"""Bounded exact probe for the homogeneous odds factor with heterogeneous weights."""
from itertools import combinations, product
from math import prod
from random import Random

rng = Random(59142)
cases = [
    (3, 3, 1, 0, 2),
    (4, 4, 1, 0, 3),
    (5, 2, 1, 0, 1),
    (5, 3, 1, 0, 2),
    (5, 3, 2, 1, 2),
    (5, 5, 1, 1, 3),
    (6, 3, 2, 1, 2),
]

def arrays(n, d, k, low, cap):
    groups = [[] for _ in range(d + 1)]
    for columns in product(tuple(combinations(range(n), k)), repeat=d):
        loads = [sum(row in column for column in columns) for row in range(n)]
        if all(low <= load <= cap for load in loads[1:]):
            groups[loads[0]].append([
                row * d + col
                for col, column in enumerate(columns)
                for row in column
            ])
    return groups

for n, d, k, low, cap in cases:
    groups = [arrays(n, d, margin, low, cap) for margin in (k, k+1)]
    numerator = (k+1)*(n-k)
    denominator = k*(n-k-1)
    tested = 0
    for rep in range(180):
        choices = [1, 2, 4, 16, 256] if rep % 2 else [0, 1, 2, 16, 256]
        weights = [rng.choice(choices) for _ in range(n*d)]
        if rep % 3 == 0:
            weights[0] = 1
            weights[1:d] = [0]*(d-1)
        counts = [[sum(prod(weights[i] for i in a) for a in layer)
                   for layer in side] for side in groups]
        red, blue = counts
        for j in range(d):
            tested += bool(red[j+1] * blue[j])
            assert (numerator * red[j+1] * blue[j]
                    <= denominator * red[j] * blue[j+1]), (n, d, k, low, cap, j, weights)
    print((n, d, k, low, cap), tested, 'nonzero adjacent comparisons passed')
