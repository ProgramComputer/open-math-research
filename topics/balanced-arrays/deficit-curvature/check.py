#!/usr/bin/env python3
"""Screen an endpoint coefficient-curvature bound against unweighted arrays."""
import argparse
import gzip
import json
import math
from pathlib import Path
import subprocess

from flint import arb, ctx, fmpz

HERE = Path(__file__).resolve().parent
REVISION = "5bcefb9ba2439f8248fed98c75d1c6b52d21023d"
RESULTS = "topics/balanced-arrays/results"
COEFFICIENT_ARCHIVES = (
    "corank-one.jsonl.gz",
    "degree_reduction.jsonl",
    "linear_tail_ranges.jsonl",
    "source_range.jsonl",
)
TRANSITION_ARCHIVES = (
    "column-extension-cap-two.jsonl.gz",
    "column-extension-corank-two.jsonl.gz",
    "column-extension-screen.jsonl.gz",
    "column-extension-seven.jsonl.gz",
)

def load(repo, commit):
    cases = {}
    archives = TRANSITION_ARCHIVES + COEFFICIENT_ARCHIVES
    for source in archives:
        data = subprocess.check_output(
            ["git", "-C", repo, "show", f"{commit}:{RESULTS}/{source}"]
        )
        if source.endswith(".gz"):
            data = gzip.decompress(data)
        for line in data.splitlines():
            row = json.loads(line)
            n, r, d = (row[name] for name in ("n", "r", "d"))
            if source in TRANSITION_ARCHIVES:
                entries = [((n, r, d), row["left"]), ((n, r, d+1), row["right"])]
            elif "coefficients" in row:
                entries = [((n, r, d), row["coefficients"])]
            else:
                continue
            for case, a in entries:
                n, r, d = case
                if len(a) != n*r//d+1 or a[0] != 1 or any(v <= 0 for v in a):
                    raise ArithmeticError((source, case, "invalid coefficient vector"))
                old, provenance = cases.setdefault(case, (a, []))
                if old != a:
                    raise ArithmeticError((source, case, "inconsistent archives"))
                if source not in provenance:
                    provenance.append(source)
    return cases

def compare(e, n, d, left, center, right):
    numerator, denominator = center**2, left*right
    common = math.gcd(numerator, denominator)
    numerator //= common
    denominator //= common
    base_top, base_bottom = e+2*d, e+d
    common = math.gcd(base_top, base_bottom)
    base_top //= common
    base_bottom //= common
    power_top, power_bottom = n*d, n+e+d
    common = math.gcd(power_top, power_bottom)
    power_top //= common
    power_bottom //= common
    for prec in (96, 192, 384):
        ctx.prec = prec
        delta = (
            (arb(numerator) / denominator).log()
            - (arb(base_top) / base_bottom).log() * power_top / power_bottom
        )
        if delta > 0:
            return "pass", "arb"
        if delta < 0:
            return "fail", "arb"
    lhs = fmpz(numerator)**power_bottom * fmpz(base_bottom)**power_top
    rhs = fmpz(denominator)**power_bottom * fmpz(base_top)**power_top
    return (
        "pass" if lhs > rhs else "fail" if lhs < rhs else "equal",
        "exact_power",
    )

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[2])
    parser.add_argument("--revision", default=REVISION,
                        help="Git revision containing the input archives")
    parser.add_argument("--output", type=Path,
                        help="write a deterministic gzip archive instead of checking the bundled one")
    args = parser.parse_args()
    commit = subprocess.check_output(
        ["git", "-C", args.repo, "rev-parse", "--verify", args.revision], text=True
    ).strip()
    selections = {
        "transitions": TRANSITION_ARCHIVES,
        "coefficients": COEFFICIENT_ARCHIVES,
        "union": TRANSITION_ARCHIVES + COEFFICIENT_ARCHIVES,
    }
    summary = {name: dict(vectors=0, nodes=0, passes=0, failures=0,
                          ties=0, power_fallbacks=0) for name in selections}
    records = []
    for (n, r, d), (a, sources) in sorted(load(args.repo, commit).items()):
        nodes = []
        for k in range(1, len(a)-1):
            e = n*r-d*k
            outcome, method = compare(e, n, d, *a[k-1:k+2])
            nodes.append([k, e, outcome, method])
        record = dict(n=n, r=r, d=d, archives=sources, degree=len(a)-1, nodes=nodes)
        records.append(json.dumps(record, separators=(",", ":")))
        for name, archive_set in selections.items():
            if not any(source in archive_set for source in sources):
                continue
            stats = summary[name]
            stats["vectors"] += 1
            stats["nodes"] += len(nodes)
            stats["passes"] += sum(node[2] == "pass" for node in nodes)
            stats["failures"] += sum(node[2] == "fail" for node in nodes)
            stats["ties"] += sum(node[2] == "equal" for node in nodes)
            stats["power_fallbacks"] += sum(node[3] == "exact_power" for node in nodes)
    replay = ("\n".join(records) + "\n").encode()
    if args.output is not None:
        with args.output.open("wb") as stream:
            with gzip.GzipFile(filename="", fileobj=stream, mode="wb", mtime=0) as output:
                output.write(replay)
    elif gzip.decompress((HERE / "screen.jsonl.gz").read_bytes()) != replay:
        raise ArithmeticError("recomputed data do not match the packaged archive")
    print(json.dumps({"commit": commit, "summary": summary}, indent=2))


if __name__ == "__main__":
    main()
