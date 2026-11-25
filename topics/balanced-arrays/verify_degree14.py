"""Verify the finite part of the degree-at-most-14 theorem from scratch.

Run with Python 3.10 or later. No packages or data files are required.
For a coefficient-by-coefficient archive comparison, pass a JSONL path:

    python verify_degree14.py results/degree_reduction.jsonl

The finite reduction uses three proved results: normalized log-concavity
and its strict coefficient-separation criterion, the endpoint-rank formulas,
and the all-dimension theorem for at most 24 rows. This script checks the
degree cutoff and every remaining triple. It counts the exceptional arrays
by separating two labeled columns from the others, then applies exact Sturm
arithmetic to the reconstructed polynomials.
"""

import argparse
import json
from collections import defaultdict
from functools import lru_cache
from math import comb, gcd
from pathlib import Path
from time import perf_counter


DEGREE_LIMIT = 14
ROW_LIMIT = 24
SEPARATION = "normalized log-concavity and strict separation"
EXPLICIT = "explicit polynomial"


def finite_domain():
    """Generate the parameters left over after the analytic cutoffs."""
    cutoff = 1
    while DEGREE_LIMIT**cutoff < 4 * (DEGREE_LIMIT - 1)**cutoff:
        cutoff += 1
    if cutoff != 19:
        raise ArithmeticError(f"Unexpected dimension cutoff {cutoff}")
    for dimension in range(3, cutoff):
        for cap in range(2, dimension):
            # floor(rows * cap / dimension) <= DEGREE_LIMIT iff
            # rows * cap <= (DEGREE_LIMIT + 1) * dimension - 1.
            largest_rows = ((DEGREE_LIMIT + 1) * dimension - 1) // cap
            for rows in range(ROW_LIMIT + 1, largest_rows + 1):
                yield rows, cap, dimension


def separates(rows, cap, dimension):
    degree = rows * cap // dimension
    unrestricted = [comb(rows, k)**dimension for k in range(degree + 1)]
    return all(unrestricted[k]**2 > 4 * unrestricted[k - 1] * unrestricted[k + 1]
               for k in range(1, degree))


@lru_cache(maxsize=8)
def binomial_table(rows):
    return tuple(tuple(comb(size, selected) for selected in range(size + 1))
                 for size in range(rows + 1))


def largest_load_groups(rows, quota, cap, dimension, choose):
    """Count partial arrays with specified sets of rows of loads cap and cap-1."""
    profiles = {(rows,) + (0,) * cap: 1}
    for inserted in range(dimension - 2):
        updated = defaultdict(int)
        last_load = min(inserted, cap - 1)
        remaining_columns = dimension - inserted
        for profile, count in profiles.items():
            selectable = rows - profile[cap]
            if selectable < quota:
                continue
            if remaining_columns < cap:
                available_capacity = sum(size * min(cap - load, remaining_columns)
                                         for load, size in enumerate(profile))
                if available_capacity < remaining_columns * quota:
                    continue
            target = list(profile)

            def distribute(load, remaining, available, weight):
                size = profile[load]
                if load == last_load:
                    if remaining <= size:
                        target[load] -= remaining
                        target[load + 1] += remaining
                        updated[tuple(target)] += weight * choose[size][remaining]
                        target[load] += remaining
                        target[load + 1] -= remaining
                    return
                available -= size
                for selected in range(max(0, remaining - available), min(size, remaining) + 1):
                    target[load] -= selected
                    target[load + 1] += selected
                    distribute(load + 1, remaining - selected, available,
                               weight * choose[size][selected])
                    target[load] += selected
                    target[load + 1] -= selected

            distribute(0, quota, selectable, count)
        profiles = updated

    totals = defaultdict(int)
    for profile, count in profiles.items():
        full, almost_full = profile[-1], profile[-2]
        if 2 * (rows - full) - almost_full >= 2 * quota:
            totals[full, almost_full] += count

    for (full, almost_full), count in totals.items():
        assignments = choose[rows][full] * choose[rows - full][almost_full]
        per_assignment, remainder = divmod(count, assignments)
        if remainder:
            raise ArithmeticError("Row-label symmetry did not divide out exactly")
        yield full, almost_full, per_assignment


def coefficient(rows, quota, cap, dimension):
    """Count arrays by the overlap size of their final two labeled columns."""
    if quota == 0:
        return 1
    choose = binomial_table(rows)
    groups = tuple(largest_load_groups(rows, quota, cap, dimension, choose))
    total = 0
    for overlap in range(max(0, 2 * quota - rows), quota + 1):
        empty = rows - 2 * quota + overlap
        at_most_one = rows - overlap
        completions = 0
        for full, almost_full, ways in groups:
            # Full rows avoid both columns. Rows of load cap-1 avoid their
            # intersection. All other rows can use either column freely.
            if full <= empty and almost_full <= at_most_one - full:
                placements = choose[empty][full] * choose[at_most_one - full][almost_full]
                completions += placements * ways
        column_pairs = choose[quota][overlap] * choose[rows - quota][quota - overlap]
        total += column_pairs * completions
    return choose[rows][quota] * total


def positive_primitive(poly):
    content = gcd(*poly)
    return [coefficient // content for coefficient in poly] if content else poly


def negative_remainder(dividend, divisor):
    """Return a positive multiple of minus the rational remainder."""
    remainder = dividend.copy()
    while len(remainder) >= len(divisor):
        offset = len(remainder) - len(divisor)
        scale = abs(divisor[-1])
        multiplier = remainder[-1] if divisor[-1] > 0 else -remainder[-1]
        remainder = [scale * coefficient for coefficient in remainder]
        for index, coefficient in enumerate(divisor, offset):
            remainder[index] -= multiplier * coefficient
        while remainder and remainder[-1] == 0:
            remainder.pop()
        remainder = positive_primitive(remainder)
    return [-coefficient for coefficient in remainder]


def variations(signs):
    nonzero = [sign > 0 for sign in signs if sign]
    return sum(first != second for first, second in zip(nonzero, nonzero[1:]))


def negative_root_count(coefficients):
    """Count negative roots of a square-free polynomial by integer Sturm steps."""
    if coefficients[0] == 0:
        raise ArithmeticError("The Sturm interval endpoint must not be a root")
    chain = [coefficients]
    if len(coefficients) > 1:
        derivative = [i * c for i, c in enumerate(coefficients) if i > 0]
        chain.append(positive_primitive(derivative))
    while len(chain[-1]) > 1:
        remainder = negative_remainder(*chain[-2:])
        if not remainder:
            raise ArithmeticError("The polynomial has a nonconstant derivative gcd")
        chain.append(remainder)
    before = variations(poly[-1] * (-1)**(len(poly) - 1) for poly in chain)
    at_zero = variations(poly[0] for poly in chain)
    return before - at_zero


def load_archive(path):
    records = {}
    with path.open() as stream:
        for line in stream:
            record = json.loads(line)
            key = record["n"], record["r"], record["d"]
            if key in records:
                raise ValueError(f"Duplicate archive triple {key}")
            records[key] = record
    return records


def verify(archive=None):
    expected_keys = list(finite_domain())
    # Reconcile the table before counting any expensive coefficients.
    if archive is not None:
        missing = set(expected_keys) - archive.keys()
        extra = archive.keys() - set(expected_keys)
        if missing or extra:
            raise ValueError(f"Archive coverage mismatch: {len(missing)} missing, {len(extra)} extra")

    separated = explicit = coefficient_count = 0
    for key in expected_keys:
        rows, cap, dimension = key
        degree = rows * cap // dimension
        method = SEPARATION if separates(*key) else EXPLICIT
        if archive is not None and archive[key]["method"] != method:
            raise ValueError(f"Incorrect archive classification at {key}")
        if method == SEPARATION:
            separated += 1
            continue

        coefficients = [coefficient(rows, k, cap, dimension) for k in range(degree + 1)]
        if any(c <= 0 for c in coefficients):
            raise ArithmeticError(f"Incomplete coefficient support at {key}")
        if archive is not None and coefficients != archive[key]["coefficients"]:
            raise ArithmeticError(f"Independently computed coefficients disagree at {key}")
        if negative_root_count(coefficients) != degree:
            raise ArithmeticError(f"The full degree of negative roots was not found at {key}")
        explicit += 1
        coefficient_count += len(coefficients)

    if (len(expected_keys), separated, explicit) != (1929, 1541, 388):
        raise ArithmeticError("Unexpected number of finite checks")
    return len(expected_keys), separated, explicit, coefficient_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path, help="optional JSONL to compare")
    args = parser.parse_args()
    started = perf_counter()
    archive = load_archive(args.archive) if args.archive is not None else None
    triples, separated, explicit, coefficients = verify(archive)
    print(f"Verified {triples} finite triples: {separated} separation tests and {explicit} "
          f"exact root counts after reconstructing {coefficients} coefficients.")
    if archive is not None:
        print("Every classification and exceptional coefficient agrees with the archive.")
    print(f"Elapsed: {perf_counter() - started:.2f} seconds.")


if __name__ == "__main__":
    main()
