"""Independently reconstruct the two row-deletion obstructions."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, gcd, lcm, perm


def matchings(quota):
    counts = [1]
    for colors in range(4):
        updated = [0] * ((colors + 1) * quota // 2 + 1)
        for edges, count in enumerate(counts):
            free = colors * quota - 2 * edges
            for added in range(min(free, quota) + 1):
                updated[edges + added] += count * comb(free, added) * perm(quota, added)
        counts = updated
    return counts


def matching_row(n):
    return [
        sum(m * perm(n, 4 * k - edges) for edges, m in enumerate(matchings(k)))
        // factorial(k)**4
        for k in range(n // 2 + 1)
    ]


def column_row(n):
    """Assign occupied row sets to labeled columns, tracking exact row loads."""
    answer = []
    for k in range(n // 2 + 1):
        subsets = list(combinations(range(n), k))
        states = Counter({(0,) * n: 1})
        for _ in range(4):
            updated = Counter()
            for loads, ways in states.items():
                for subset in subsets:
                    if any(loads[i] == 2 for i in subset):
                        continue
                    new_loads = list(loads)
                    for i in subset:
                        new_loads[i] += 1
                    updated[tuple(new_loads)] += ways
            states = updated
        answer.append(sum(states.values()))
    return answer


def inverse_symbol(left, right):
    degree = len(right) - 1
    rationals = [Fraction(comb(degree, k) * a, right[k]) for k, a in enumerate(left)]
    denominator = lcm(*(v.denominator for v in rationals))
    integers = [int(v * denominator) for v in rationals]
    content = gcd(*integers)
    return [v // content for v in integers]


def multiplier_witness():
    left = matching_row(7)
    right = matching_row(8)
    if left != column_row(7) or right != column_row(8):
        raise ArithmeticError("the independent array counts disagree")
    if left != [1, 2226, 102690, 106260] or right != [1, 3864, 380100, 1543920, 44730]:
        raise ArithmeticError((left, right))
    a, b, c, d = inverse_symbol(left, right)
    if (a, b, c, d) != (19128985, 44079835, 31007979, 5266195):
        raise ArithmeticError("unexpected primitive symbol")
    value = a - b + c - d
    first = b - 2*c + 3*d
    second = 2*c - 6*d
    gap = first**2 - value*second
    if (value, first, second, gap) != (790934, -2137538, 30418788, -19490184966548):
        raise ArithmeticError((value, first, second, gap))
    print(f"Deletion symbol: Laguerre expression at -1 = {gap}")


def corank_one_count(n, k):
    if k > 2*n // 3:
        return 0
    return sum((-1)**j * comb(n, j) * comb(n-j, k-j)**3 for j in range(k+1))


def thinning_witness():
    p = Fraction(1, 500)
    a, b, c = (
        sum(comb(3, j) * p**j * (1-p)**(3-j) * corank_one_count(3+j, k)
            for j in range(4))
        for k in (2, 3, 4)
    )
    gap = a*c - b*b
    if gap != Fraction(32575077, 781250000000000):
        raise ArithmeticError((a, b, c, gap))
    print(f"Independent row retention: reverse log-concavity gap = {gap}")


if __name__ == "__main__":
    multiplier_witness()
    thinning_witness()
