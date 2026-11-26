#!/usr/bin/env python3
"""Replay preliminary balanced-array signs at rational approximations to phase nodes.

Generate uses binary64 phase bisection, then evaluates the polynomial at the
resulting exact rational point. Verify repeats only the exact arithmetic and
can optionally compare the bundled finite-36 vectors to their source file.
Neither mode encloses a true phase node or proves its polynomial sign.
"""

from argparse import ArgumentParser
import cmath
from fractions import Fraction
import gzip
from hashlib import sha256
from io import TextIOWrapper
import json
import math
from pathlib import Path


FORMAT = "balanced-angular-sign-screen-v1"
SOURCE_PATH = "topics/balanced-arrays/finite-36/exact-vectors.jsonl"
SOURCE_SHA256 = "eea2b4519ef71be6904638ac07c57c1a852e2976fa59b98eca8fb406a69aadf0"
FINITE_VECTOR_COUNT = 18
LOG_TILT_LOWER = -32.0
LOG_TILT_UPPER = 32.0
BISECTION_STEPS = 54

METADATA = {
    "type": "metadata",
    "format": FORMAT,
    "endpoint_cases": {"n": [2, 48], "d": "2..min(10,n)", "r": ["1", "d-1"]},
    "finite_vector_source": {
        "path": SOURCE_PATH,
        "sha256": SOURCE_SHA256,
        "vectors": FINITE_VECTOR_COUNT,
    },
    "phase_search": {
        "target": "k*pi",
        "precision": "binary64 floating point",
        "log_tilt_bracket": [LOG_TILT_LOWER, LOG_TILT_UPPER],
        "bisection_steps": BISECTION_STEPS,
    },
    "nodes": ["quota", "tilt_numerator", "tilt_denominator", "sign"],
    "evaluation_point": "-(tilt_numerator/tilt_denominator)^d",
    "scope": "exact signs at sampled rational points, no enclosure of true phase nodes",
}


def endpoint_triples():
    return {
        (n, d, r)
        for n in range(2, 49)
        for d in range(2, min(10, n) + 1)
        for r in {1, d - 1}
    }


def endpoint_coefficients(n, d, r):
    """Use disjoint column choices at rank one and inclusion-exclusion at corank one."""
    if r == 1:
        return [
            math.prod(math.comb(n - j * quota, quota) for j in range(d))
            for quota in range(n // d + 1)
        ]
    if r == d - 1:
        return [
            sum(
                (-1) ** j * math.comb(n, j) * math.comb(n - j, quota - j) ** d
                for j in range(quota + 1)
            )
            for quota in range(n * r // d + 1)
        ]
    raise ValueError(f"Not an endpoint cap: {(n, d, r)}")


def finite_36_vectors(path):
    """Load only the 18 rows used in the original screen, from the pinned source."""
    source = path.read_bytes()
    if sha256(source).hexdigest() != SOURCE_SHA256:
        raise ValueError(f"Unexpected SHA-256 for {path}. Expected {SOURCE_SHA256}.")
    vectors = {}
    for line in source.splitlines():
        row = json.loads(line)
        key = row["n"], row["d"], row["r"]
        if key in vectors:
            raise ValueError(f"Repeated finite-36 vector: {key}")
        vectors[key] = row["coefficients"]
    if len(vectors) != FINITE_VECTOR_COUNT:
        raise ValueError(f"Expected {FINITE_VECTOR_COUNT} finite-36 vectors.")
    return vectors


def row_series(coefficients, log_tilt, theta):
    # A positive real rescaling avoids large exponentials and preserves the argument.
    shift = len(coefficients) - 1 if log_tilt >= 0 else 0
    return sum(
        coefficient * cmath.exp(complex((j - shift) * log_tilt, j * theta))
        for j, coefficient in enumerate(coefficients)
    )


def phase_at(log_tilt, n, d, h, b):
    theta = math.pi / d
    nu = (d - 1) / 2
    return (
        (n + nu) * cmath.phase(row_series(h, log_tilt, theta))
        - nu * cmath.phase(row_series(b, log_tilt, theta))
        - nu * theta
    )


def sampled_tilt(quota, n, d, h, b):
    """Return the exact dyadic corresponding to the floating-point search result."""
    lo, hi = LOG_TILT_LOWER, LOG_TILT_UPPER
    target = quota * math.pi
    if not phase_at(lo, n, d, h, b) < target < phase_at(hi, n, d, h, b):
        raise ArithmeticError(f"Floating-point phase target not bracketed: {(n, d, quota)}")
    for _ in range(BISECTION_STEPS):
        mid = (lo + hi) / 2
        if phase_at(mid, n, d, h, b) < target:
            lo = mid
        else:
            hi = mid
    return Fraction.from_float(math.exp((lo + hi) / 2))


def exact_node_sign(coefficients, d, numerator, denominator):
    """Evaluate at -(numerator/denominator)**d with an integer Horner recurrence."""
    q_num = -(numerator**d)
    q_den = denominator**d
    value = coefficients[-1]
    denominator_power = 1
    for coefficient in reversed(coefficients[:-1]):
        denominator_power *= q_den
        value = q_num * value + coefficient * denominator_power
    return (value > 0) - (value < 0)


def check_vector(key, coefficients):
    n, d, r = key
    if not 1 <= r < d <= n or len(coefficients) != n * r // d + 1:
        raise ArithmeticError(f"Invalid cap, dimensions, or degree: {key}")
    if coefficients[0] != 1 or any(type(c) is not int or c <= 0 for c in coefficients):
        raise ArithmeticError(f"Invalid coefficients: {key}")


def make_cases(finite):
    endpoints = endpoint_triples()
    if endpoints & finite.keys():
        raise ValueError("The pinned finite-36 source overlaps the endpoint family.")
    for key in sorted(endpoints | finite.keys()):
        n, d, r = key
        if key in finite:
            coefficients = finite[key]
            source = "finite-36"
        else:
            coefficients = endpoint_coefficients(n, d, r)
            source = "endpoint-formula"
        check_vector(key, coefficients)
        h = [math.comb(d, j) for j in range(r + 1)]
        b = [math.comb(d - 2, j) for j in range(r)]
        nodes = []
        for quota in range(1, len(coefficients) - 1):
            tilt = sampled_tilt(quota, n, d, h, b)
            numerator, denominator = tilt.numerator, tilt.denominator
            sign = exact_node_sign(coefficients, d, numerator, denominator)
            nodes.append([quota, numerator, denominator, sign])
        yield {
            "type": "case",
            "n": n,
            "d": d,
            "r": r,
            "source": source,
            "coefficients": coefficients,
            "nodes": nodes,
        }


def summarize(cases):
    counts = {"type": "summary", "vectors": 0, "with_internal_nodes": 0, "nodes": 0, "mismatches": 0}
    for case in cases:
        nodes = case["nodes"]
        counts["vectors"] += 1
        counts["with_internal_nodes"] += bool(nodes)
        counts["nodes"] += len(nodes)
        counts["mismatches"] += sum(sign != (-1) ** quota for quota, _, _, sign in nodes)
        yield case
    yield counts


def write_archive(output, finite):
    with output.open("xb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as archive:
            with TextIOWrapper(archive, encoding="utf-8", newline="\n") as stream:
                stream.write(json.dumps(METADATA, separators=(",", ":")) + "\n")
                for record in summarize(make_cases(finite)):
                    stream.write(json.dumps(record, separators=(",", ":")) + "\n")
    return record


def checked_cases(stream, finite):
    endpoints = endpoint_triples()
    seen_endpoints = set()
    seen_finite = set()
    previous_key = (0, 0, 0)
    for line in stream:
        case = json.loads(line)
        if case["type"] == "summary":
            break
        if case["type"] != "case":
            raise ValueError("Unexpected archive record.")
        key = case["n"], case["d"], case["r"]
        if key <= previous_key:
            raise ValueError(f"Archive cases are repeated or unordered at {key}.")
        previous_key = key
        coefficients = case["coefficients"]
        check_vector(key, coefficients)
        if key in endpoints:
            if case["source"] != "endpoint-formula" or coefficients != endpoint_coefficients(*key):
                raise ArithmeticError(f"Endpoint coefficient replay differs at {key}.")
            seen_endpoints.add(key)
        else:
            if key[0] != 36 or case["source"] != "finite-36":
                raise ValueError(f"Unexpected non-endpoint case {key}.")
            if finite is not None and coefficients != finite.get(key):
                raise ArithmeticError(f"Finite-36 coefficient replay differs at {key}.")
            seen_finite.add(key)
        nodes = case["nodes"]
        if len(nodes) != max(0, len(coefficients) - 2):
            raise ValueError(f"Incomplete node list at {key}.")
        previous_tilt = Fraction(0)
        for quota, (recorded_quota, numerator, denominator, sign) in enumerate(nodes, 1):
            if denominator <= 0 or denominator & (denominator - 1):
                raise ValueError(f"Invalid dyadic tilt at {key + (quota,)}.")
            tilt = Fraction(numerator, denominator)
            if recorded_quota != quota or tilt <= previous_tilt:
                raise ValueError(f"Invalid quota or tilt order at {key + (quota,)}.")
            if exact_node_sign(coefficients, key[1], numerator, denominator) != sign:
                raise ArithmeticError(f"Exact sign replay differs at {key + (quota,)}.")
            previous_tilt = tilt
        yield case
    else:
        raise ValueError("Archive ended before its summary record.")
    if seen_endpoints != endpoints or len(seen_finite) != FINITE_VECTOR_COUNT:
        raise ValueError("Archive does not contain the complete screened inventory.")
    if finite is not None and seen_finite != finite.keys():
        raise ValueError("Archive does not contain the pinned set of finite-36 cases.")
    if any(line.strip() for line in stream):
        raise ValueError("Unexpected records after the summary.")
    yield case


def verify_archive(archive, finite):
    with gzip.open(archive, "rt", encoding="utf-8") as stream:
        if json.loads(next(stream)) != METADATA:
            raise ValueError("Archive metadata do not match this screen.")
        records = checked_cases(stream, finite)
        counts = {"type": "summary", "vectors": 0, "with_internal_nodes": 0, "nodes": 0, "mismatches": 0}
        for record in records:
            if record["type"] == "summary":
                if record != counts:
                    raise ValueError("Archive summary does not match its records.")
                return counts
            nodes = record["nodes"]
            counts["vectors"] += 1
            counts["with_internal_nodes"] += bool(nodes)
            counts["nodes"] += len(nodes)
            counts["mismatches"] += sum(sign != (-1) ** quota for quota, _, _, sign in nodes)
    raise ValueError("Archive contains no summary.")


def main():
    parser = ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate", help="regenerate sampled points and exact signs")
    generate.add_argument("--finite-vectors", required=True, type=Path)
    generate.add_argument("--output", required=True, type=Path)
    verify = commands.add_parser("verify", help="replay exact signs in an existing archive")
    verify.add_argument("archive", type=Path)
    verify.add_argument("--finite-vectors", type=Path, help="also compare the pinned finite-36 input")
    args = parser.parse_args()

    finite = finite_36_vectors(args.finite_vectors) if args.finite_vectors else None
    if args.command == "generate":
        summary = write_archive(args.output, finite)
    else:
        summary = verify_archive(args.archive, finite)

    print(
        f"{summary['vectors']} triples, {summary['with_internal_nodes']} with internal quotas, "
        f"{summary['nodes']} sampled internal nodes, {summary['mismatches']} sign mismatches."
    )
    return int(bool(summary["mismatches"]))


if __name__ == "__main__":
    raise SystemExit(main())
