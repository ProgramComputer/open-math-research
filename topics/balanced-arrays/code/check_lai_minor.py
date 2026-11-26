"""Check the all-edge coefficient of one weighted matching Toeplitz minor."""

from collections import Counter
from functools import cache
from itertools import permutations


# Example 2.1 of Matherne and Morales, arXiv:2607.21508v1.
EDGES = (
    (1, 8), (2, 7), (3, 6), (3, 10), (4, 5), (4, 9),
    (5, 9), (6, 10), (7, 9), (7, 10), (8, 9), (8, 10),
)
ALL_EDGES = (1 << len(EDGES)) - 1


def is_matching(mask):
    endpoints = [v for i, edge in enumerate(EDGES) if mask & (1 << i) for v in edge]
    return len(endpoints) == len(set(endpoints))


MATCHING_MASKS = {mask for mask in range(ALL_EDGES + 1) if is_matching(mask)}


@cache
def partitions(mask, sizes):
    """Count ordered disjoint matchings with these sizes and exact union."""
    if not sizes:
        return int(mask == 0)
    if len(sizes) == 1:
        return int(mask in MATCHING_MASKS and mask.bit_count() == sizes[0])
    return sum(
        partitions(mask ^ subset, sizes[1:])
        for subset in MATCHING_MASKS
        if subset & mask == subset and subset.bit_count() == sizes[0]
    )


def coefficient(order, offset):
    """Extract the product of all edge variables by the Leibniz formula."""
    terms = Counter()
    for perm in permutations(range(order)):
        inversions = sum(perm[i] > perm[j] for i in range(order) for j in range(i + 1, order))
        sizes = tuple(sorted(offset - i + j for i, j in enumerate(perm)))
        terms[sizes] += (-1) ** inversions
    return [
        (sizes, multiplier, partitions(ALL_EDGES, sizes))
        for sizes, multiplier in sorted(terms.items())
        if multiplier
    ]


if __name__ == "__main__":
    terms = coefficient(4, 3)
    for sizes, multiplier, count in terms:
        print(sizes, multiplier, count)
    result = sum(multiplier * count for _, multiplier, count in terms)
    if result != -64:
        raise SystemExit(f"unexpected coefficient {result}")
    print(f"all-edge coefficient = {result}")
