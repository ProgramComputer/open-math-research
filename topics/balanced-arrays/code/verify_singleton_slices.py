"""Exact small-row reconstructions for the Bessel singleton formulas."""

import json
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import factorial, prod

COLORS = tuple(range(4))
EDGES = tuple(combinations(COLORS, 2))
OPPOSITE = tuple((edge, tuple(i for i in COLORS if i not in edge))
                 for edge in EDGES if 0 in edge)
UNIFORM_TERMS = {
    0: [(0, (0, 0, 0), 1)],
    1: [(1, (0, 0, 1), 6), (2, (1, 1, 1), 2)],
    2: [(1, (0, 0, 0), 1), (2, (0, 0, 2), Fraction(3, 2)),
        (2, (0, 1, 1), 6), (3, (1, 1, 2), 2),
        (4, (2, 2, 2), Fraction(1, 6))],
    3: [(2, (0, 0, 1), Fraction(3, 2)), (3, (0, 0, 3), Fraction(1, 6)),
        (3, (0, 1, 2), 2), (3, (1, 1, 1), Fraction(7, 6)),
        (4, (1, 1, 3), Fraction(1, 4)), (4, (1, 2, 2), Fraction(1, 2)),
        (5, (2, 2, 3), Fraction(1, 10)), (6, (3, 3, 3), Fraction(1, 180))],
}


def injection(n, used):
    return factorial(n) // factorial(n - used)


def product_coefficient(degree, differences, weights):
    coefficients = [Fraction(1)] + [Fraction(0)] * degree
    for difference, weight in zip(differences, weights):
        factor = [Fraction(weight ** m, factorial(m) * factorial(m + difference))
                  for m in range(degree + 1)]
        coefficients = [sum(coefficients[j] * factor[i - j] for j in range(i + 1))
                        for i in range(degree + 1)]
    return coefficients[degree]


def quota_formula(n, half_singletons, terms, weights):
    values = []
    for quota in range(n // 2 + 1):
        used = 2 * quota + half_singletons
        coefficient = Fraction(0)
        if used <= n:
            coefficient = injection(n, used) * sum(
                weight * product_coefficient(quota - baseline, differences, weights)
                for baseline, differences, weight in terms if baseline <= quota
            )
        if coefficient.denominator != 1:
            raise ArithmeticError("Singleton slice certificate mismatch")
        values.append(coefficient.numerator)
    return values


def direct_rows(max_rows, max_singletons, singleton_weights, edge_weights):
    row_types = [((), 1)]
    row_types += [((i,), singleton_weights[i]) for i in COLORS]
    row_types += [(edge, edge_weights[edge]) for edge in EDGES]
    states = {((0, 0, 0, 0), 0): 1}
    for n in range(max_rows + 1):
        yield n, states
        new = defaultdict(int)
        for (degrees, singletons), count in states.items():
            for subset, weight in row_types:
                total_singletons = singletons + (len(subset) == 1)
                if not weight or total_singletons > max_singletons:
                    continue
                next_degrees = tuple(x + (i in subset) for i, x in enumerate(degrees))
                if max(next_degrees) <= max_rows // 2:
                    new[next_degrees, total_singletons] += weight * count
        states = new


def rows_with_fixed_counts(max_rows, target, edge_weights):
    states = {((0, 0, 0, 0), (0, 0, 0, 0)): 1}
    row_types = [((), 1)] + [((i,), 1) for i in COLORS]
    row_types += [(edge, edge_weights[edge]) for edge in EDGES]
    for n in range(max_rows + 1):
        yield n, [
            states.get(((k, k, k, k), target), 0)
            for k in range(n // 2 + 1)
        ]
        new = defaultdict(int)
        for (degrees, singletons), count in states.items():
            for subset, weight in row_types:
                if not weight:
                    continue
                if len(subset) == 1:
                    i = subset[0]
                    if singletons[i] == target[i]:
                        continue
                    next_singletons = tuple(s + (j == i) for j, s in enumerate(singletons))
                else:
                    next_singletons = singletons
                next_degrees = tuple(x + (i in subset) for i, x in enumerate(degrees))
                if max(next_degrees) <= max_rows // 2:
                    new[next_degrees, next_singletons] += weight * count
        states = new


def fixed_count_formula(n, target, edge_weights):
    half_singletons = sum(target) // 2
    differences = [half_singletons - target[i] - target[j]
                   for ((i, j), _) in OPPOSITE]
    baseline = (half_singletons + sum(map(abs, differences))) // 2
    weight = Fraction(1, prod(factorial(s) for s in target))
    for (left, right), delta in zip(OPPOSITE, differences):
        weight *= edge_weights[left] ** max(delta, 0) * edge_weights[right] ** max(-delta, 0)
    products = tuple(edge_weights[a] * edge_weights[b] for a, b in OPPOSITE)
    return quota_formula(n, half_singletons, [(baseline, tuple(map(abs, differences)), weight)], products)


def weighted_two_terms(singleton_weights, edge_weights):
    terms = []
    for index, (left, right) in enumerate(OPPOSITE):
        a = prod(singleton_weights[i] for i in left) * edge_weights[right]
        a += prod(singleton_weights[i] for i in right) * edge_weights[left]
        terms.append((1, tuple(int(j == index) for j in range(3)), a))
    b = sum(Fraction(singleton_weights[i] ** 2, 2) *
            prod(edge_weights[e] for e in EDGES if i not in e)
            for i in COLORS)
    terms.append((2, (1, 1, 1), b))
    return terms


def main():
    output = {"uniform_slices": [], "fixed_counts": [], "weighted_two": []}
    for n, states in direct_rows(12, 6, (1, 1, 1, 1), dict.fromkeys(EDGES, 1)):
        for s, terms in UNIFORM_TERMS.items():
            direct = [states.get(((k, k, k, k), 2 * s), 0)
                      for k in range(n // 2 + 1)]
            if direct != quota_formula(n, s, terms, (1, 1, 1)):
                raise ArithmeticError("Singleton slice certificate mismatch")
            output["uniform_slices"].append({"n": n, "singletons": 2 * s, "coefficients": direct})
    fixed_tests = [
        ((2, 1, 1, 0), (2, 3, 5, 7, 11, 13)),
        ((1, 1, 0, 0), (1, 3, 5, 7, 11, 0)),
        ((1, 1, 0, 0), (0, 1, 0, 1, 0, 2)),
    ]
    for target, weights in fixed_tests:
        edge_weights = dict(zip(EDGES, weights))
        for n, direct in rows_with_fixed_counts(8, target, edge_weights):
            if direct != fixed_count_formula(n, target, edge_weights):
                raise ArithmeticError("Singleton slice certificate mismatch")
            output["fixed_counts"].append({
                "n": n, "singletons": target, "weights": weights, "coefficients": direct
            })
    singleton_weights = (2, 3, 5, 7)
    edge_weights = dict(zip(EDGES, (2, 3, 5, 7, 11, 13)))
    terms = weighted_two_terms(singleton_weights, edge_weights)
    products = tuple(edge_weights[a] * edge_weights[b] for a, b in OPPOSITE)
    for n, states in direct_rows(8, 2, singleton_weights, edge_weights):
        direct = [states.get(((k, k, k, k), 2), 0) for k in range(n // 2 + 1)]
        if direct != quota_formula(n, 1, terms, products):
            raise ArithmeticError("Singleton slice certificate mismatch")
        output["weighted_two"].append({"n": n, "coefficients": direct})
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
