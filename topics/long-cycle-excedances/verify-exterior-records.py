"""Verify that the four exterior records cover the full requested finite band."""
from pathlib import Path
import re

ROOT = Path(__file__).with_name("exterior-records")
RANGES = ((49, 240), (241, 370), (371, 510), (511, 733))
PATTERN = re.compile(
    r"k=(\d+): (\d+) pairs; cumulative (\d+), subdivisions (\d+), "
    r"bracket digest ([0-9a-f]{64})"
)


def main():
    all_pairs = all_subdivisions = 0
    for first, last in RANGES:
        record = ROOT / f"k{first:03}-{last:03}.txt"
        lines = record.read_text().splitlines()
        if len(lines) != last-first+1:
            raise ArithmeticError(record)
        cumulative = subdivisions = 0
        for k, line in zip(range(first,last+1),lines):
            group = PATTERN.fullmatch(line)
            if group is None:
                raise ArithmeticError(line)
            lo, hi = max(3*k-1,192), min(4*k-1,2199)
            pairs = hi-lo+1
            cumulative += pairs
            if tuple(map(int, group.groups()[:3])) != (k, pairs, cumulative):
                raise ArithmeticError(line)
            updated = int(group[4])
            if updated <= subdivisions:
                raise ArithmeticError(line)
            subdivisions = updated
        all_pairs += cumulative
        all_subdivisions += subdivisions
    if (all_pairs, all_subdivisions) != (200800, 21809970):
        raise ArithmeticError((all_pairs, all_subdivisions))
    print(f"{all_pairs} consecutive pairs, {19*all_pairs} one-sided old brackets, "
          f"{all_subdivisions} bisections.")


if __name__ == "__main__":
    main()
