"""Verify the endpoint implication on the supplying source and compiler pins."""

import argparse
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMPACT = runpy.run_path(str(HERE.parent / "compact-rows/check.py"))
KERNEL_INPUTS = (
    (HERE.parent / "fast-insertion", "RoundedHorner", {"roundedRatio_eq", "rounded_error", "signed_lower", "horner_first"}),
    (HERE.parent / "fast-insertion", "IntegerTail", {"integer_tail_margin"}),
    (HERE, "PositiveCeilHorner", {"upperHorner_cons", "horner_positive_le", "uncertainty_upper",
                                   "compressed_lower", "compressed_integer_margin"}),
    (HERE, "CompactPoint", {"original_signed_of_packed_margin"}),
    (HERE, "RepositoryPackedPoint", {"original_signed_of_packed_words"}),
)


def check(project, imports):
    COMPACT["check"](project, imports)
    for folder, module, expected in KERNEL_INPUTS:
        COMPACT["audit_module"](project, module, expected, folder / (module + ".lean"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("imports", type=Path, nargs="?")
    args = parser.parse_args()
    check(args.project.resolve(), args.imports.resolve() if args.imports else None)
