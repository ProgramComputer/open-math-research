"""Certify both signs of the distinguished-cycle term in the insertion recurrence."""
import argparse
from gzip import GzipFile
import json
from math import comb
from pathlib import Path
from runpy import run_path

TOPIC = Path(__file__).resolve().parent
ARCHIVE = TOPIC / "insertion-lag.jsonl.gz"
LIMIT = 46
cycle_helpers = run_path(str(TOPIC / "verify.py"))
add_product = cycle_helpers["add_product"]
interlacing_chain = cycle_helpers["interlacing_chain"]
eulerian_rows = run_path(str(TOPIC / "verify_cycle_deletions.py"))["eulerian_rows"]


def records(last):
    unrestricted = eulerian_rows(last)
    for k in range(3, last + 1):
        rows = [[1]] + [[] for _ in range(k - 1)]
        for size in range(k, last + 1):
            old = rows[-1]
            insertion = [0] * size
            for h, count in enumerate(old):
                insertion[h] += h * count
                insertion[h + 1] += (size - 1 - h) * count
            lag = [0] * size
            add_product(lag, unrestricted[k-1], rows[size-k], comb(size-1, k-1))
            row = [a + b for a, b in zip(insertion, lag)]
            rows.append(row)
            if row[1] != 1 or row[1:] != row[:0:-1]:
                raise ArithmeticError(f"Wrong reciprocity or extreme coefficients at {(size,k)}")
            if size == k:
                yield dict(n=size, k=k, coefficients=row, nonzero_lag_pair=None)
                continue
            reverse = [a - b for a, b in zip(insertion, lag)]
            actual = interlacing_chain(row[1:], old[1:])
            reversed_lag = interlacing_chain(reverse[1:], old[1:]) if any(lag) else actual
            yield dict(n=size, k=k, coefficients=row, nonzero_lag_pair=any(lag),
                       positive_chain_degrees=actual, negative_chain_degrees=reversed_lag)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="create a new certificate")
    parser.add_argument("--archive", type=Path, default=ARCHIVE)
    args = parser.parse_args()
    rows = pairs = nonzero = 0
    with args.archive.open("xb" if args.write else "rb") as raw:
        with GzipFile(filename="", mode="wb" if args.write else "rb", fileobj=raw,
                      **({"mtime": 0} if args.write else {})) as archive:
            for item in records(LIMIT):
                if args.write:
                    archive.write((json.dumps(item, separators=(",", ":"))+"\n").encode())
                elif json.loads(archive.readline()) != item:
                    raise ArithmeticError(f"Certificate mismatch at {(item['n'],item['k'])}")
                rows += 1
                pairs += item["nonzero_lag_pair"] is not None
                nonzero += bool(item["nonzero_lag_pair"])
            if not args.write and archive.read(1):
                raise ArithmeticError("Unexpected extra archive entries")
    print(f"Certified {rows} rows and {pairs} insertion pairs, "
          f"including {nonzero} pairs with a nonzero new-cycle term.")


if __name__ == "__main__":
    main()
