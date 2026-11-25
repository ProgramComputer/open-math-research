"""Replay the full n <= 24 balanced-array reduction from its labeled-column definition."""

import json
import sys
from math import comb
from pathlib import Path

topic = Path(__file__).resolve().parent
sys.path.extend((str(topic / "code"), str(topic.parents[1] / "shared" / "python")))

from coefficients import column_count
from roots import root_report


def verify(records):
    pending = {(n, r, d) for n in range(25) for d in range(2, n) for r in range(2, d)}
    separated = 0
    explicit = 0
    for line in records:
        row = json.loads(line)
        n, r, d = key = (row["n"], row["r"], row["d"])
        if key not in pending:
            raise ValueError(f"Duplicate or unexpected parameters {key}")
        pending.remove(key)
        degree = n * r // d
        lower_bounds_suffice = all(
            comb(n, k)**(2 * d) > 4 * (comb(n, k - 1) * comb(n, k + 1))**d
            for k in range(1, degree)
        )
        if lower_bounds_suffice:
            if row["method"] != "normalized log-concavity and strict separation":
                raise ValueError(f"Incorrect method at {key}")
            separated += 1
            continue
        if row["method"] != "explicit polynomial":
            raise ValueError(f"Missing exact certificate at {key}")
        coefficients = [column_count(n, k, r, d) for k in range(degree + 1)]
        if coefficients != row["coefficients"] or min(coefficients) <= 0:
            raise ArithmeticError(f"Incorrect coefficients at {key}")
        sturm = root_report(coefficients)
        if sturm != row["root_report"] or sturm["distinct_real_roots"] != degree:
            raise ArithmeticError(f"Incorrect root count at {key}")
        explicit += 1
    if pending:
        raise ValueError(f"Missing {len(pending)} triples")
    print(f"Verified all {separated + explicit} finite triples. "
          f"{separated} pass separation and {explicit} pass exact coefficient and Sturm checks.")


if __name__ == "__main__":
    with (topic / "results" / "linear_tail_ranges.jsonl").open() as records:
        verify(records)
