"""Portable archive-aware exact residual coverage for balanced arrays."""
import argparse
from collections import Counter
import gzip
import json
from math import comb
from pathlib import Path
import subprocess
import sys

ARCHIVE_REV = "ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2"
SOURCES = (
    "source_range.jsonl", "linear_tail_ranges.jsonl", "degree_reduction.jsonl",
    "column-extension-cap-two.jsonl.gz", "column-extension-corank-two.jsonl.gz",
    "column-extension-screen.jsonl.gz", "column-extension-seven.jsonl.gz",
)
PREFIX = "topics/balanced-arrays/"
SEPARATION = "normalized log-concavity and strict separation"


def archive_data(repo, rev, name):
    return subprocess.check_output(["git", "-C", str(repo), "show", f"{rev}:{PREFIX}{name}"])


def inherited(repo, rev, start, end):
    known = {}

    def add(key, coefficients, source):
        if not start <= key[0] <= end:
            return
        if len(coefficients) != key[0] * key[1] // key[2] + 1:
            raise ArithmeticError(f"Incorrect inherited degree: {key}")
        if key in known and known[key][0] != coefficients:
            raise ArithmeticError(f"Conflicting inherited coefficients: {key}")
        known.setdefault(key, (coefficients, source))

    for name in SOURCES:
        source = f"results/{name}"
        content = archive_data(repo, rev, source)
        if name.endswith(".gz"):
            content = gzip.decompress(content)
        for line in content.splitlines():
            row = json.loads(line)
            n, r, d = (row[key] for key in ("n", "r", "d"))
            if "coefficients" in row:
                add((n, r, d), row["coefficients"], source)
            elif "left" in row:
                add((n, r, d), row["left"], source)
                add((n, r, d + 1), row["right"], source)
    return known


def covers_by_separation(n, r, d):
    degree = n * r // d
    return all((comb(n, k)**2)**d > 4*(comb(n,k-1)*comb(n,k+1))**d
               for k in range(1, degree))


def method(n, r, d, known):
    key = (n, r, d)
    if r == 1:
        return "rank-one theorem"
    if r == d:
        return "full-cap theorem"
    if r == d-1:
        return "corank-one theorem"
    if (r, d) == (2, 4):
        return "four-column cap-two theorem"
    if n*r//d <= 14:
        return "degree-at-most-14 theorem"
    if covers_by_separation(n, r, d):
        return "orientation separation"
    if key in known:
        return "inherited coefficients, fresh exact Sturm"
    return "fresh exact count and Sturm"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--revision", default=ARCHIVE_REV)
    parser.add_argument("--start", type=int, default=25)
    parser.add_argument("--end", type=int, default=35)
    parser.add_argument("--output", type=Path, default=Path("records.jsonl"))
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--inventory", action="store_true")
    parser.add_argument(
        "--check", nargs="?", type=Path, const=Path(__file__).with_name("records.jsonl.gz"),
        help="check saved records without recounting fresh cases",
    )
    args = parser.parse_args()
    if args.start < 25 or args.end < args.start:
        parser.error("require 25 <= start <= end")
    repo = args.repo.resolve()
    revision = subprocess.check_output(["git", "-C", str(repo), "rev-parse", args.revision],
                                       text=True).strip()
    for path in ("shared/python/roots.py", PREFIX + "code/coefficients.py"):
        expected = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", f"{revision}:{path}"], text=True).strip()
        actual = subprocess.check_output(
            ["git", "-C", str(repo), "hash-object", path], text=True).strip()
        if actual != expected:
            raise ArithmeticError(f"Source differs from pinned revision at {path}")
    sys.path.insert(0, str(repo / "shared/python"))
    sys.path.insert(0, str(repo / PREFIX / "code"))
    from roots import root_report
    from coefficients import column_count
    known = inherited(repo, revision, args.start, args.end)
    inputs = [(n,r,d) for n in range(args.start,args.end+1)
              for d in range(2,n) for r in range(1,d+1)]
    if args.check:
        if args.check.suffix == ".gz":
            with gzip.open(args.check, "rt", encoding="utf-8") as archive:
                records = iter(archive.read().splitlines())
        else:
            records = iter(args.check.read_text().splitlines())
        for n in range(args.start, args.end + 1):
            tail = dict(n=n, d_min=n, method="orientation separation, all d >= n")
            if json.loads(next(records)) != tail or (n + 1)**(2*n) <= 4*n**(2*n):
                raise ArithmeticError(f"Invalid infinite dimension tail at n={n}")
            for nn, r, d in inputs:
                if nn != n:
                    continue
                row = json.loads(next(records))
                key = (n, r, d)
                how = method(*key, known)
                expected = dict(n=n, r=r, d=d, degree=n*r//d, method=how)
                if how.startswith("fresh exact") or how.startswith("inherited"):
                    coefficients = row["coefficients"]
                    if key in known:
                        inherited_coefficients, source = known[key]
                        if coefficients != inherited_coefficients:
                            raise ArithmeticError(f"Inherited coefficient mismatch at {key}")
                        expected["source"] = f"{revision}:{PREFIX}{source}"
                    report = root_report(coefficients)
                    if (len(coefficients) != expected["degree"] + 1 or
                            min(coefficients) <= 0 or
                            report["distinct_real_roots"] != expected["degree"]):
                        raise ArithmeticError(f"Saved polynomial failed at {key}")
                    expected.update(coefficients=coefficients, root_report=report)
                if row != expected:
                    raise ArithmeticError(f"Unexpected saved record at {key}")
        if next(records, None) is not None:
            raise ArithmeticError("Extra saved records")
        print(f"Validated saved coverage and exact root certificates for n={args.start}..{args.end}")
        return
    if args.inventory:
        for n in range(args.start,args.end+1):
            todo = [(r,d) for nn,r,d in inputs
                    if nn == n and method(n,r,d,known) == "fresh exact count and Sturm"]
            print(n, len(todo), todo)
        return
    engine = None
    if args.engine:
        engine = subprocess.Popen([str(args.engine.resolve())], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)

    def count(n, k, r, d):
        if engine is None or n > 62 or r > 15:
            return column_count(n,k,r,d)
        engine.stdin.write(f"{n} {r} {d} {k}\n")
        engine.stdin.flush()
        return int(engine.stdout.readline())

    if engine:
        for n,k,r,d in [(6,2,2,4),(8,3,3,5),(10,2,4,6),(12,6,3,5),(18,6,4,7),(25,12,2,4)]:
            if count(n,k,r,d) != column_count(n,k,r,d):
                raise ArithmeticError(f"Engine mismatch at {(n,k,r,d)}")
    try:
        with args.output.open("w", buffering=1) as output:
            for n in range(args.start,args.end+1):
                tally = Counter()
                # d >= n is an infinite analytic tail. For k internal, each
                # factor is at least (1+1/n), and (1+1/n)^(2*n) > 4.
                if (n + 1)**(2*n) <= 4*n**(2*n):
                    raise ArithmeticError("Infinite dimension tail test failed")
                print(json.dumps(dict(n=n, d_min=n, method="orientation separation, all d >= n")),
                      file=output)
                for nn,r,d in inputs:
                    if nn != n:
                        continue
                    key = (n,r,d)
                    how = method(n,r,d,known)
                    tally[how] += 1
                    row = dict(n=n,r=r,d=d,degree=n*r//d,method=how)
                    if how.startswith("fresh exact") or how.startswith("inherited"):
                        if key in known:
                            coefficients, source = known[key]
                            row["source"] = f"{revision}:{PREFIX}{source}"
                        else:
                            print("counting", key, flush=True)
                            coefficients = [count(n,k,r,d) for k in range(1+row["degree"])]
                        report = root_report(coefficients)
                        row.update(coefficients=coefficients, root_report=report)
                        if min(coefficients) <= 0 or report["distinct_real_roots"] != row["degree"]:
                            print(json.dumps(row), file=output)
                            raise ArithmeticError(f"Simple negative root test failed at {key}")
                    print(json.dumps(row,separators=(",",":")), file=output)
                print(n, dict(tally), flush=True)
    finally:
        if engine:
            engine.stdin.close()
            engine.wait()
            if engine.returncode:
                raise ArithmeticError(f"Counting engine exited with status {engine.returncode}")


if __name__ == "__main__":
    main()
