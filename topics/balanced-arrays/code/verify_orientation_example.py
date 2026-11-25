"""Direct four-row check of the saturation vectors in the orientation proof."""

from itertools import combinations, product


def distribution(quotas):
    counts = [0] * 5
    for columns in product(*(combinations(range(4), k) for k in quotas)):
        occupancy = [0] * 4
        for column in columns:
            for row in column:
                occupancy[row] += 1
        if max(occupancy) <= 3:
            counts[occupancy.count(3)] += 1
    return counts


if __name__ == '__main__':
    for quotas, expected in (
        ((1, 1, 2, 2, 2), [204, 1404, 780, 0, 0]),
        ((2, 1, 2, 2, 2), [0, 936, 1632, 144, 0]),
        ((1, 1, 3, 2, 2), [0, 480, 780, 60, 0]),
        ((2, 1, 3, 2, 2), [0, 0, 936, 348, 0]),
        ((3, 1, 2, 2, 2), [0, 0, 936, 348, 0]),
    ):
        if distribution(quotas) != expected:
            raise ArithmeticError(quotas)
    print('Verified all five saturated-row distributions by direct enumeration.')
