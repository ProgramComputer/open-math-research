"""Check archived Schur determinants by adding labeled rows directly."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
from math import comb, prod
from pathlib import Path

import gzip
import json

CASES = {(4, 2, 14): 507, (5, 3, 11): 194, (5, 2, 11): 194, (6, 3, 9): 96}


@lru_cache(None)
def quota_count(n, d, r, k):
    if k < 0 or d * k > n * r:
        return 0
    supports = [subset for size in range(r + 1)
                for subset in combinations(range(d), size)]
    states = {(0,) * d: 1}
    for row in range(n):
        following = Counter()
        for totals, multiplicity in states.items():
            for subset in supports:
                target = list(totals)
                for j in subset:
                    target[j] += 1
                if all(k - (n - row - 1) <= value <= k for value in target):
                    following[tuple(target)] += multiplicity
        states = following
    return states.get((k,) * d, 0)


def direct_minor(n, d, r, shape):
    value = 0
    for permutation in permutations(range(len(shape))):
        term = prod(quota_count(n, d, r, shape[i] - i + j)
                    for i, j in enumerate(permutation))
        odd = sum(a > b for i, a in enumerate(permutation) for b in permutation[i + 1:]) % 2
        value += -term if odd else term
    return value


def main():
    n_checks = n_nonzero = n_records = 0
    for (d, r, cutoff), expected_count in CASES.items():
        path = Path(__file__).with_name(f"binomial-schur-{d}-{r}-{cutoff}.jsonl.gz")
        selected = {(1, 1, 1), (2, 1), (3, 1)}
        seen = set()
        with gzip.open(path, "rt", encoding="utf-8") as archive:
            for line in archive:
                row = json.loads(line)
                shape = tuple(row["partition"])
                coefficients = row["binomial_coefficients"]
                if ((row["d"], row["r"]) != (d, r)
                    or shape in seen
                    or not 1 <= sum(shape) <= cutoff
                    or len(coefficients) != d * sum(shape) + 1
                    or row["negative_indices"] or min(coefficients) < 0):
                    raise ArithmeticError((path, shape))
                seen.add(shape)
                if shape not in selected:
                    continue
                for n in (3, 5):
                    value = sum(comb(n, j) * c for j, c in enumerate(coefficients) if j <= n)
                    if value != direct_minor(n, d, r, shape):
                        raise ArithmeticError((n, d, r, shape))
                    n_checks += 1
                    n_nonzero += value != 0
        if len(seen) != expected_count or not selected <= seen:
            raise ArithmeticError(path)
        n_records += len(seen)
    print(f"{n_records} archived identities, {n_checks} direct determinant checks ({n_nonzero} nonzero)")


if __name__ == "__main__":
    main()
