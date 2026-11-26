from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb

def array_count_by_columns(n, d, cap, quota):
    """Assign labeled column subsets, discarding overfull row states."""
    columns = list(combinations(range(n), quota))
    states = Counter({(0,) * n: 1})
    for _ in range(d):
        following = Counter()
        for loads, count in states.items():
            for column in columns:
                if any(loads[row] == cap for row in column):
                    continue
                updated = list(loads)
                for row in column:
                    updated[row] += 1
                following[tuple(updated)] += count
        states = following
    return sum(states.values())

def check_retained_exponent_one():
    n, d, cap = 4, 7, 5
    coefficients = [array_count_by_columns(n, d, cap, k) for k in range(3)]
    assert coefficients == [1, 16296, 211176]
    retained = [Fraction(v, comb(n, k)**6) for k, v in enumerate(coefficients)]
    discriminant = retained[1]**2 - 4 * retained[0] * retained[2]
    assert discriminant == Fraction(-48335287, 21233664)
    print("retained exponent one", coefficients, [str(x) for x in retained], discriminant)

if __name__ == "__main__":
    check_retained_exponent_one()
