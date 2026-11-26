"""Check the saved corank-two vectors by inclusion-exclusion on forbidden rows."""
import argparse
import gzip
import json
from pathlib import Path
import sys

code = Path(__file__).resolve().parent
sys.path.extend((str(code), str(code.parents[2] / "shared/python")))
from verify_corank_two_symbol import corank_two_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    reader = gzip.open if args.archive.suffix == ".gz" else open
    vectors = entries = 0
    with reader(args.archive, "rt") as records:
        for line in records:
            row = json.loads(line)
            if "coefficients" not in row or row["d"] - row["r"] != 2:
                continue
            n, d = row["n"], row["d"]
            expected = [corank_two_count(n, k, d) for k in range(1 + n*(d-2)//d)]
            if expected != row["coefficients"]:
                raise ArithmeticError(f"Inclusion-exclusion disagrees at n={n}, d={d}")
            vectors += 1
            entries += len(expected)
    if not vectors:
        raise ValueError("Input has no corank-two coefficient vector")
    print(f"Recounted {vectors} corank-two polynomials and {entries} coefficients by inclusion-exclusion.")


if __name__ == "__main__":
    main()
