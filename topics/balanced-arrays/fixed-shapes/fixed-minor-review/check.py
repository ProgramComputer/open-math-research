"""Independent exact cutoff and Newton coefficients for small straight shapes."""
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations
import json
from math import factorial, prod


def partitions(weight, width=None):
    if weight == 0:
        yield ()
        return
    for first in range(min(weight, width or weight), 0, -1):
        for rest in partitions(weight-first, first):
            yield (first, *rest)


@cache
def terms(shape):
    result = []
    for perm in permutations(range(len(shape))):
        quotas = tuple(a-i+j for i, (a, j) in enumerate(zip(shape, perm)))
        if min(quotas) < 0:
            continue
        inversions = sum(perm[i] > perm[j] for i in range(len(perm)) for j in range(i+1, len(perm)))
        result.append((quotas, (-1)**inversions))
    return result


def bad_weight(shape, d):
    numerator = prod(map(factorial, shape))
    return sum(Fraction(numerator, prod(map(factorial, q)))**d
               for q, sign in terms(shape) if sign < 0)


@cache
def count(n, d, r, k):
    if k == 0:
        return 1
    if n < k or n*r < d*k:
        return 0
    supports = [s for j in range(r+1) for s in combinations(range(d), j)]
    layers = {(0,)*d: 1}
    for height in range(n):
        next_layer = {}
        for profile, multiplicity in layers.items():
            for support in supports:
                margins = list(profile)
                for j in support:
                    margins[j] += 1
                if max(margins) > k or min(margins) + n-height-1 < k:
                    continue
                key = tuple(sorted(margins))
                next_layer[key] = next_layer.get(key, 0) + multiplicity
        layers = next_layer
    return layers.get((k,)*d, 0)


def minor(n, d, r, shape):
    return sum(sign*prod(count(n, d, r, k) for k in q) for q, sign in terms(shape))


def newton(values):
    result = []
    while values:
        result.append(values[0])
        values = [right-left for left, right in zip(values, values[1:])]
    return result


def main():
    for d, weight in [(2, 5), (3, 9)]:
        exceptions = []
        for size in range(1, weight+1):
            for shape in partitions(size):
                # Lengthy all-one tails are checked by the same enumeration.
                bad = bad_weight(shape, d)
                if bad > 1:
                    assert size == weight
                    exceptions.append((shape, bad))
        print(json.dumps({"dimension": d, "first_exception_weight": weight,
                          "exceptions": [[s, str(b)] for s, b in exceptions]}))
        for shape, _ in exceptions:
            for r in range(1, d+1):
                nmax = d*weight
                sample = [minor(n, d, r, shape) for n in range(nmax+1)]
                coeff = newton(sample)
                assert all(a >= 0 for a in coeff), (d, r, shape, coeff)
                first = next(i for i, x in enumerate(sample) if x)
                print(json.dumps(dict(d=d, r=r, shape=shape, first_positive_height=first,
                                      first_positive_value=sample[first],
                                      positive_Newton_coefficients=sum(x > 0 for x in coeff),
                                      leading_Newton_coefficient=coeff[-1])))


if __name__ == "__main__":
    main()
