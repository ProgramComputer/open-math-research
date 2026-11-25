"""Exact counts for binary arrays with equal column sums and bounded rows."""

from collections import defaultdict
from functools import lru_cache
from itertools import combinations
from math import comb


def degree_bound(n: int, r: int, d: int) -> int:
    """Return the degree of the generating polynomial in the column sum."""
    if n < 0 or r < 0 or d < 1:
        raise ValueError("n and r must be nonnegative and d must be positive")
    return min(n, n * r // d)


def special_count(n: int, k: int, r: int, d: int) -> int | None:
    """Return an applicable elementary count, or None."""
    bound = degree_bound(n, r, d)
    if k < 0 or k > bound:
        return 0
    if k == 0:
        return 1
    if r >= d:
        return comb(n, k) ** d
    if r == 1:
        ways = 1
        for column in range(d):
            ways *= comb(n - column * k, k)
        return ways
    if r == d - 1:
        return sum(
            (-1) ** j * comb(n, j) * comb(n - j, k - j) ** d
            for j in range(k + 1)
        )
    return None


def row_count(n: int, k: int, r: int, d: int) -> int:
    """Append rows using a sparse histogram of column deficits."""
    bound = degree_bound(n, r, d)
    if k < 0 or k > bound:
        return 0
    if k == 0:
        return 1
    r = min(r, d)

    @lru_cache(maxsize=8192)
    def moves(state, forced_bucket, minimum):
        target = list(state)
        forced = state[forced_bucket] if forced_bucket else 0
        if forced:
            target[forced_bucket] -= forced
            target[forced_bucket - 1] += forced
        buckets = [
            (j, size) for j, size in enumerate(state)
            if j and j != forced_bucket and size
        ]
        suffix = [0] * (len(buckets) + 1)
        for i in range(len(buckets) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + buckets[i][1]
        result = []

        def visit(i, lower, upper, weight):
            if i == len(buckets):
                result.append((tuple(target), weight))
                return
            j, size = buckets[i]
            for selected in range(max(0, lower - suffix[i + 1]), min(size, upper) + 1):
                target[j] -= selected
                target[j - 1] += selected
                visit(i + 1, lower - selected, upper - selected, weight * comb(size, selected))
                target[j] += selected
                target[j - 1] -= selected

        lower = max(0, minimum - forced)
        upper = r - forced
        if lower <= min(upper, suffix[0]):
            visit(0, lower, upper, 1)
        return result

    layer = {(0,) * k + (d,): 1}
    for rows_left in range(n, 2, -1):
        forced_bucket = rows_left if rows_left <= k else 0
        next_layer = defaultdict(int)
        for state, ways in layer.items():
            remaining = sum(j * size for j, size in enumerate(state))
            minimum = max(0, remaining - (rows_left - 1) * r)
            for target, multiplier in moves(state, forced_bucket, minimum):
                next_layer[target] += ways * multiplier
        layer = next_layer

    if n == 1:
        return 1  # Positive feasible k forces the single row to contain all d ones.
    total = 0
    for state, ways in layer.items():
        singles = state[1]
        free = r - (state[2] if k >= 2 else 0)
        splits = sum(comb(singles, j) for j in range(max(0, singles - free), min(singles, free) + 1))
        total += ways * splits
    return total


def column_count(n: int, k: int, r: int, d: int) -> int:
    """Append columns using a sparse histogram of remaining row capacities."""
    bound = degree_bound(n, r, d)
    if k < 0 or k > bound:
        return 0
    if k == 0:
        return 1
    r = min(r, d)

    def moves(state, columns_left):
        target = list(state)
        clipped = columns_left < len(state)
        top_size = target.pop() if clipped else 0
        if clipped:
            # Every row in the top bucket has the same next capacity.
            target[-1] += top_size
        buckets = [(j, size) for j, size in enumerate(state) if j and j < columns_left and size]
        suffix = [0] * (len(buckets) + 1)
        for i in range(len(buckets) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + buckets[i][1]

        capacity = sum(j * size for j, size in enumerate(target))
        lower = max(0, k - top_size)
        upper = min(k, capacity - (columns_left - 1) * k)

        def visit(i, selected_so_far, weight):
            if i == len(buckets):
                yield tuple(target), weight * comb(top_size, k - selected_so_far)
                return
            j, size = buckets[i]
            least = max(0, lower - selected_so_far - suffix[i + 1])
            most = min(size, upper - selected_so_far)
            for selected in range(least, most + 1):
                target[j] -= selected
                target[j - 1] += selected
                yield from visit(i + 1, selected_so_far + selected, weight * comb(size, selected))
                target[j] += selected
                target[j - 1] -= selected

        if lower <= min(upper, suffix[0]):
            yield from visit(0, 0, 1)

    layer = {(0,) * r + (n,): 1}
    for columns_left in range(d, 1, -1):
        next_layer = defaultdict(int)
        for state, ways in layer.items():
            for target, multiplier in moves(state, columns_left):
                next_layer[target] += ways * multiplier
        layer = next_layer
    return sum(ways * comb(n - state[0], k) for state, ways in layer.items())


def brute_count(n: int, k: int, r: int, d: int) -> int:
    """Count small instances by enumerating actual row subsets."""
    bound = degree_bound(n, r, d)
    if k < 0 or k > bound:
        return 0
    if k == 0:
        return 1
    row_options = [row for size in range(min(r, d) + 1) for row in combinations(range(d), size)]

    def visit(rows_left, sums):
        if rows_left == 0:
            return int(all(value == k for value in sums))
        total = 0
        for row in row_options:
            next_sums = sums.copy()
            for column in row:
                next_sums[column] += 1
            if all(k - rows_left + 1 <= value <= k for value in next_sums):
                total += visit(rows_left - 1, next_sums)
        return total

    return visit(n, [0] * d)


def count(n: int, k: int, r: int, d: int, method: str = "auto") -> int:
    """Return the exact coefficient using the requested method."""
    if method == "row":
        return row_count(n, k, r, d)
    if method == "column":
        return column_count(n, k, r, d)
    if method == "brute":
        return brute_count(n, k, r, d)
    if method != "auto":
        raise ValueError(f"unknown counting method {method!r}")

    simple = special_count(n, k, r, d)
    if simple is not None:
        return simple
    row_width = min(k, n - k)
    row_states = comb(d + row_width, row_width)
    column_states = comb(n + r, r)
    if row_states <= column_states:
        return row_count(n, k, r, d)
    return column_count(n, k, r, d)


def polynomial_coefficients(n: int, r: int, d: int, method: str = "auto") -> tuple[int, ...]:
    """Return the coefficients in order of ascending column sum."""
    return tuple(count(n, k, r, d, method) for k in range(degree_bound(n, r, d) + 1))
