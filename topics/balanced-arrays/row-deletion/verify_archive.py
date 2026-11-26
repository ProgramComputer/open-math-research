"""Replay the exact 360-pair backward row symbol screen."""

import gzip
import json
from pathlib import Path
import sys

from check_witnesses import inverse_symbol

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "shared/python"))
from roots import root_report


def main():
    source = HERE.parent / "results/source_range.jsonl"
    coefficients = {}
    with source.open() as stream:
        for line in stream:
            row = json.loads(line)
            key = row["n"], row["r"], row["d"]
            if key in coefficients:
                raise ValueError(f"duplicate source row {key}")
            coefficients[key] = row["coefficients"]

    regenerated = []
    for (n, r, d), left in sorted(coefficients.items()):
        right = coefficients.get((n+1, r, d))
        if right is None:
            continue
        symbol = inverse_symbol(left, right)
        regenerated.append(dict(n=n, r=r, d=d, left=left, right=right,
                                symbol=symbol, root_report=root_report(symbol)))

    with gzip.open(HERE / "inverse-row-symbols.jsonl.gz", "rt") as stream:
        archived = [json.loads(line) for line in stream]
    if regenerated != archived:
        raise ArithmeticError("the archived symbols or root reports disagree")

    failures = sum(not row["root_report"]["real_rooted"] for row in regenerated)
    if (len(regenerated), failures) != (360, 225):
        raise ArithmeticError((len(regenerated), failures))
    print(f"Replayed {len(regenerated)} symbols: {failures} with nonreal zeros, "
          f"{len(regenerated) - failures} with all real zeros.")


if __name__ == "__main__":
    main()
