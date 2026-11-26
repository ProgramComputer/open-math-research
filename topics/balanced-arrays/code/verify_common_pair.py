"""Independent exact certificates for four columns with uniform pair weight."""
from argparse import ArgumentParser
from functools import cache
from fractions import Fraction
import gzip
import json
from math import comb, factorial, gcd, perm
from pathlib import Path


FIRST_ROW = 26
LAST_ROW = 33
DEFAULT_UNWEIGHTED_ARCHIVE = (
    Path(__file__).resolve().parent.parent / "results" / "four_column_mehler.jsonl"
)
EXAMPLE_FILES = {
    "weight-176-row-33.json": (33, Fraction(176)),
    "weight-216-row-32.json": (32, Fraction(216)),
    "weight-264-row-33.json": (33, Fraction(264)),
    "weight-351-over-2-row-33.json": (33, Fraction(351, 2)),
    "weight-431-over-2-row-32.json": (32, Fraction(431, 2)),
}


@cache
def weight_coefficients(n, k):
    """a(n,k;t) by the two column pairs 12 and 34."""
    result = [0] * (2*k+1)
    for first_pure in range(k+1):
        first_support = 2*(k-first_pure)
        for second_pure in range(min(k,n-first_pure)+1):
            second_support = 2*(k-second_pure)
            remaining = n-first_pure-second_pure
            if first_support > remaining or second_support > remaining:
                continue
            first_singles = comb(first_support, first_support//2)
            second_singles = comb(second_support, second_support//2)
            base = (
                comb(n, first_pure)*comb(n-first_pure, second_pure)
                * comb(remaining, first_support)*first_singles*second_singles
            )
            least = max(0, first_support+second_support-remaining)
            most = min(first_support, second_support)
            for intersection in range(least, most+1):
                exponent = first_pure+second_pure+intersection
                result[exponent] += (
                    base*comb(first_support, intersection)
                    * comb(remaining-first_support, second_support-intersection)
                )
    return result


def row(n, weight):
    weight = Fraction(weight)
    if weight < 0:
        raise ValueError("negative weights are outside the intended scope")
    values = []
    for k in range(n//2+1):
        coefficient = weight_coefficients(n, k)
        accum = sum(
            value*weight.numerator**p*weight.denominator**(2*k-p)
            for p, value in enumerate(coefficient)
        )
        # This implements q -> denominator^2*q, a positive rescaling.
        values.append(accum)
    return values


def primitive(polynomial):
    while polynomial and polynomial[-1] == 0:
        polynomial.pop()
    content = gcd(*polynomial)
    if content > 1:
        return [coefficient//content for coefficient in polynomial]
    return polynomial


def signed_remainder(dividend, divisor):
    """Return a positive multiple of the negative rational remainder."""
    result = dividend.copy()
    leading = divisor[-1]
    while len(result) >= len(divisor):
        offset = len(result)-len(divisor)
        multiplier = result[-1]*(1 if leading > 0 else -1)
        result = [abs(leading)*coefficient for coefficient in result]
        for i, coefficient in enumerate(divisor):
            result[offset+i] -= multiplier*coefficient
        result = primitive(result)
    return [-coefficient for coefficient in result]


def integer_chain(coefficients):
    p = primitive(coefficients.copy())
    previous = [power*coefficient for power,coefficient in enumerate(p) if power]
    while p:
        yield p
        p, previous = previous, signed_remainder(p,previous) if previous else previous


def flint_chain(coefficients):
    from flint import fmpq_poly

    p = fmpq_poly(coefficients)
    previous = p.derivative()
    while p:
        yield list(p)
        p, previous = previous, -(p % previous) if previous else previous


def root_certificate(coefficients, accelerated=False):
    """Return Sturm variation counts and the degree of the final gcd."""
    chain = flint_chain(coefficients) if accelerated else integer_chain(coefficients)
    leading_signs = []
    trailing_signs = []
    negative_infinity_signs = []
    for polynomial in chain:
        sign_lc = "+" if polynomial[-1] > 0 else "-"
        degree = len(polynomial)-1
        sign_negative = sign_lc if degree % 2 == 0 else ("-" if sign_lc == "+" else "+")
        leading_signs.append(sign_lc)
        trailing_signs.append("+" if polynomial[0] > 0 else ("-" if polynomial[0] < 0 else "0"))
        negative_infinity_signs.append(sign_negative)
        gcd_degree = degree

    def variations(signs):
        nonzero = [sign for sign in signs if sign != "0"]
        return sum(a != b for a,b in zip(nonzero,nonzero[1:]))

    v_neg, v_0, v_pos = map(variations, (negative_infinity_signs,trailing_signs,leading_signs))
    return {
        "gcd_degree": gcd_degree,
        "signs_negative_infinity": "".join(negative_infinity_signs),
        "signs_zero": "".join(trailing_signs),
        "signs_positive_infinity": "".join(leading_signs),
        "variations": [v_neg,v_0,v_pos],
        "negative_distinct": v_neg-v_0,
        "positive_distinct": v_0-v_pos,
    }


@cache
def matching_counts(k):
    """Size counts for labeled matchings of the complete four-partite graph."""
    counts = [1]
    for color in range(4):
        vertices = color*k
        updated = [0] * ((vertices+k)//2+1)
        for old_pairs, count in enumerate(counts):
            free_vertices = vertices-2*old_pairs
            for new_pairs in range(min(k, free_vertices)+1):
                updated[old_pairs+new_pairs] += (
                    count*comb(free_vertices, new_pairs)*perm(k, new_pairs)
                )
        counts = updated
    return counts


def matching_weight_coefficients(n, k):
    """Independent check from matchings followed by injection into row labels."""
    coefficients = []
    for pairs, count in enumerate(matching_counts(k)):
        occupied = 4*k-pairs
        value, remainder = divmod(count*perm(n, occupied), factorial(k)**4)
        if remainder:
            raise ArithmeticError(f"label quotient is noninteger for {n=}, {k=}, {pairs=}")
        coefficients.append(value)
    return coefficients


def coefficient_vectors():
    """Factorized row data for the scan, checked against independent matchings."""
    vectors = []
    for n in range(FIRST_ROW, LAST_ROW+1):
        by_quota = []
        for k in range(n//2+1):
            vector = weight_coefficients(n, k)
            if vector != matching_weight_coefficients(n, k):
                raise ArithmeticError(f"column-pair and matching counts disagree for {n=}, {k=}")
            by_quota.append(vector)
        vectors.append({"n": n, "by_quota": by_quota})
    return vectors


def check_unweighted(archive):
    """Retain and validate the original coefficients on the targeted rows."""
    with archive.open() as infile:
        originals = {}
        for line in infile:
            data = json.loads(line)
            if FIRST_ROW <= data["n"] <= LAST_ROW:
                originals[data["n"]] = data["a"]
    verified = {}
    for n in range(FIRST_ROW, LAST_ROW+1):
        candidate = row(n, 1)
        if originals.get(n) != candidate:
            raise ValueError(f"original coefficients disagree at n={n}")
        checks = root_certificate(candidate)
        if checks["negative_distinct"] != n//2 or checks["gcd_degree"] != 0:
            raise ValueError(f"original root check failed at n={n}")
        verified[n] = {"coefficients": candidate, "sturm": checks}
    return verified


def certificate(n, t):
    coefficients = row(n, t)
    return {"n": n, "t": str(t), "coefficients": coefficients, "sturm": root_certificate(coefficients)}


def verify_examples(directory):
    coefficient_vectors()
    for name, (n, weight) in EXAMPLE_FILES.items():
        computed = certificate(n, weight)
        checks = computed["sturm"]
        if (len(computed["coefficients"]) != 17 or checks["gcd_degree"] != 0
                or checks["variations"] != [15, 1, 1]):
            raise ValueError(f"weighted counterexample check failed for {n=}, {weight=}")
        with (directory / name).open() as source:
            if computed != json.load(source):
                raise ValueError(f"certificate mismatch in {name}")
    print(f"Verified {len(EXAMPLE_FILES)} counterexamples and all factorized coefficient vectors.")


def discriminant_sign(polynomial):
    value = polynomial.discriminant()
    return (value > 0) - (value < 0)


def discriminant_grid(first_row, last_row, max_weight, stop_after_negative):
    from flint import fmpz_poly

    records = []
    for n in range(first_row, last_row+1):
        zeros = []
        negatives = []
        for t in range(2, max_weight+1):
            sign = discriminant_sign(fmpz_poly(row(n,t)))
            if sign == 0:
                zeros.append(t)
            if sign < 0:
                negatives.append(t)
                if stop_after_negative:
                    break
        records.append({
            "n": n, "first_weight": 2, "last_weight": t, "step": 1,
            "zero_weights": zeros, "negative_weights": negatives,
        })
    return records


def sturm_grid(first_row, last_row, max_weight):
    from flint import fmpz_poly

    records = []
    for n in range(first_row, last_row+1):
        degree = n//2
        default = {"gcd_degree": 0, "negative_distinct": degree, "positive_distinct": 0}
        exceptions = []
        for t in range(2, max_weight+1):
            coefficients = row(n, t)
            checks = root_certificate(coefficients, accelerated=True)
            square_free_degree = degree - checks["gcd_degree"]
            if checks["gcd_degree"]:
                p = fmpz_poly(coefficients)
                square_free = p // p.gcd(p.derivative())
                checks = root_certificate(list(square_free), accelerated=True)
                checks["gcd_degree"] = degree-square_free_degree
            result = {key: checks[key] for key in default}
            if result != default:
                exceptions.append({"t": t, **result})
            if checks["negative_distinct"] != square_free_degree:
                break
        records.append({
            "n": n, "first_weight": 2, "last_weight": t, "step": 1,
            "degree": degree, "default": default, "exceptions": exceptions,
        })
    return records


def discriminant_probes():
    """Exact replay of the original dyadic and separated spot probes."""
    from flint import fmpz_poly

    dyadic = []
    spots = []
    spot_weights = (192, 216, 264, 320, 400, 512, 640, 700, 768, 1024, 1536, 2048)
    for n, lower, upper in ((32, 215, 216), (33, 175, 176)):
        left, right = Fraction(lower), Fraction(upper)
        dyadic_cases = []
        for _ in range(16):
            t = (left+right)/2
            sign = discriminant_sign(fmpz_poly(row(n, t)))
            dyadic_cases.append({"t": str(t), "sign": sign})
            if sign < 0:
                right = t
            else:
                left = t
        dyadic.append({"n": n, "initial_bracket": [lower,upper], "cases": dyadic_cases})
        spot_cases = [{"t": t, "sign": discriminant_sign(fmpz_poly(row(n,t)))} for t in spot_weights]
        spots.append({"n": n, "cases": spot_cases})
    return dyadic, spots


def scan_ledger():
    vectors = coefficient_vectors()
    initial_disc = discriminant_grid(FIRST_ROW, LAST_ROW, 264, stop_after_negative=True)
    full = sturm_grid(FIRST_ROW, LAST_ROW, 264)
    extended_disc = discriminant_grid(FIRST_ROW, 31, 2048, stop_after_negative=False)
    dyadic, spots = discriminant_probes()
    return {
        "schema": 1,
        "model": "Labeled four-column binary arrays, equal quotas, row cap two, common weight t for all pair types.",
        "coefficient_basis": "vectors[n].by_quota[k][p] is the coefficient of q^k t^p in row n; use the n field to look up a vector.",
        "coefficient_methods": ["Column-pair supports and their intersection", "Labeled matchings and row injection, exact agreement"],
        "rational_weights": "t=A/B in lowest terms. Substitute q -> B^2 q to produce integer coefficients; root counts are invariant.",
        "vectors": vectors,
        "scans": {
            "initial_discriminant": {
                "method": "Exact integer discriminant sign. Stop after the first negative in each inclusive integer range. Unlisted signs are positive.",
                "rows": initial_disc,
            },
            "sturm": {
                "method": "Exact rational Sturm counts after removing any gcd with the derivative. Stop after the first nonreal example in each inclusive integer range.",
                "rows": full,
            },
            "extended_discriminant": {
                "method": "Exact integer discriminant sign at every integer weight in each inclusive range. Unlisted signs are positive.",
                "rows": extended_disc,
            },
            "dyadic_discriminant": {
                "method": "Exact integer discriminant signs on the positively rescaled rational-weight rows. Sixteen bisection probes per row.",
                "rows": dyadic,
            },
            "spot_discriminant": {
                "method": "Exact integer discriminant signs at the listed integer weights.",
                "rows": spots,
            },
        },
    }


def verify_discovery(path):
    """Replay the stopped discovery grid from its prescribed parameter order."""
    from flint import fmpz_poly

    count = 0
    with gzip.open(path, "rt") as source:
        for n in range(4, 101):
            weights = {1, 2, 3, 4, 6, 9, 16, 25, 36, 49, 64, 100}
            weights.update(multiplier*n for multiplier in (1, 2, 4, 8, 16, 64, 256))
            for t in sorted(weights):
                coefficients = row(n, t)
                polynomial = fmpz_poly(coefficients)
                squarefree = polynomial // polynomial.gcd(polynomial.derivative())
                sturm = root_certificate(list(squarefree), accelerated=True)
                real = sturm["negative_distinct"] + sturm["positive_distinct"]
                record = {"n": n, "pair_weight": t, "coefficients": list(map(str, coefficients)),
                          "degree": polynomial.degree(), "squarefree_degree": squarefree.degree(),
                          "real": real}
                if record != json.loads(source.readline()):
                    raise ValueError(f"discovery record mismatch for {(n, t)}")
                count += 1
                if real < squarefree.degree():
                    if source.readline():
                        raise ValueError("extra records beyond discovery stopping condition")
                    print(f"Verified {count} observations through n={n}, t={t}.")
                    return
    raise ValueError("no discovery in the prescribed grid")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--certificate", nargs=2, metavar=("N","T"))
    modes.add_argument("--verify-examples", type=Path, metavar="CERTIFICATE_DIRECTORY")
    modes.add_argument("--unweighted", action="store_true")
    modes.add_argument("--scan-ledger", action="store_true")
    modes.add_argument("--verify-ledger", type=Path, metavar="LEDGER_FILE")
    modes.add_argument("--verify-discovery", type=Path, metavar="GZIP_ARCHIVE")
    parser.add_argument("--source-archive", type=Path, default=DEFAULT_UNWEIGHTED_ARCHIVE)
    args = parser.parse_args()
    if args.certificate:
        n, t = int(args.certificate[0]), Fraction(args.certificate[1])
        print(json.dumps(certificate(n,t), indent=2))
    elif args.verify_examples:
        verify_examples(args.verify_examples)
    elif args.unweighted:
        print(json.dumps(check_unweighted(args.source_archive), sort_keys=True, indent=2))
    elif args.scan_ledger:
        print(json.dumps(scan_ledger(), separators=(",", ":")))
    elif args.verify_discovery:
        verify_discovery(args.verify_discovery)
    else:
        with args.verify_ledger.open() as source:
            archived = json.load(source)
        if archived != scan_ledger():
            raise ValueError("scan ledger mismatch")
        print("Verified the coefficient vectors, recorded parameters and every exact scan result.")
