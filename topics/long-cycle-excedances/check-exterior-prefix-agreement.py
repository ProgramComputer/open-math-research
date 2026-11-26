"""Cross-check the insertion prefixes against independent rolling cycle counts."""
from math import comb
from pathlib import Path
from runpy import run_path
from sys import argv

from flint import fmpz_poly


def main(cycle_generator):
    local = run_path(str(Path(__file__).with_name("check-three-cycle-exterior.py")))
    other = run_path(cycle_generator)
    keep, eulerian, next_e = local["KEEP"], local["eulerian"], local["next_e"]
    max_old = 2199
    eulers = eulerian((max_old+1)//3)
    checked = four_cycles = 0
    for k, prefixes in other["band_prefixes"](max_old+1, keep, first_n=192, first_k=49):
        lo = max(192, 3*k-1)
        hi = min(max_old, 4*k-1)
        if lo > hi:
            continue
        if set(prefixes) != set(range(lo, hi+2)):
            raise ArithmeticError(("prefix coverage", k))
        rows = [fmpz_poly(1)] + [fmpz_poly() for _ in range(k-1)]
        for n in range(k-1, hi+1):
            lag = comb(n, k-1)*eulers[k-1].mul_low(rows[n+1-k], keep+1)
            row = next_e(rows[n], n, lag)
            rows.append(row)
            if lo <= n+1:
                if row.right_shift(1) != prefixes[n+1]:
                    raise ArithmeticError(f"prefix disagreement at {(n+1,k)}")
                checked += 1
                four_cycles += n+1 == 4*k
    disjoint_pairs = sum(
        max(0, min(max_old, 4*k-1)-max(192, 3*k-1)+1)
        for k in range(49, 734)
    )
    if checked != disjoint_pairs + 685 or four_cycles != 502:
        raise ArithmeticError(("total coverage", checked, four_cycles))
    print(f"Independent prefix agreement: {checked} rows for {disjoint_pairs} consecutive pairs.")
    print(f"Checked {four_cycles} new rows with four cycles allowed.")


if __name__ == "__main__":
    if len(argv) > 2:
        raise SystemExit("supply at most one alternate coefficient generator")
    main(argv[1] if len(argv) == 2 else str(Path(__file__).with_name("three_cycle_prefix.py")))
