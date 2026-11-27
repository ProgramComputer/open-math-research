#!/usr/bin/env python3
"""Verify the twice-integrated coefficient bounds for the original row."""
import argparse
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE / "check-real-axis.py"))
CIRCLE = (
    "FourierPoleMoment", "FourierPolePair", "FourierFinitePoleBound",
    "FourierPoleUniform", "FourierInfinitePoleBound", "FourierComplexPoleBound",
    "FourierLatticeWeights", "FourierOddPoleProduct", "FourierSquaredSum",
    "FourierPoleDifferentiation", "FourierDerivativeBound", "FourierLatticeDerivative",
    "FourierCircleShift", "FourierCircleContrast", "FourierAdjacentIdentity",
    "FourierLatticeSplit", "FourierNormComparison", "FourierPoleContrast",
)
CHECKED = (
    ("FourierOddKernelCalculus", "odd_kernel_calculus"),
    ("FourierOriginalCoefficientBounds", "original_fourier_coefficient_bounds"),
)


def main(project, retained_imports):
    BASE["main"](project, original_log=True, retained_imports=retained_imports, continuation=True)
    build = BASE["build_local"]
    for module in CIRCLE:
        build(project, HERE.parent / "fourier-circle" / (module + ".lean"), module, ())
    for module, theorem in CHECKED:
        build(project, HERE / (module + ".lean"), module, (theorem,))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="verified common-pin import archive")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    main(args.project.resolve(), retained)
