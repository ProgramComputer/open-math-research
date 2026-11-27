#!/usr/bin/env python3
"""Verify the twice-integrated coefficient bounds for the original row."""
import argparse
from pathlib import Path
import re
import runpy
import subprocess


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
    ("FourierOddKernelCalculus", ("odd_kernel_calculus",)),
    ("FourierOddKernelMoments", ("odd_kernel_moment_integrals",)),
    ("FourierOriginalCoefficientBounds", (
        "original_fourier_contrast_weight", "original_fourier_coefficient_bounds",
        "original_fourier_bounds_of_moments",
    )),
)


def compile_coefficients(project):
    """Stage the Fourier imports and targets in an already initialized project."""
    build = BASE["build_local"]
    inputs = [(HERE.parent / "fourier-circle", module, ()) for module in CIRCLE]
    inputs += [(HERE, module, theorems) for module, theorems in CHECKED]
    failed = set()
    for folder, module, theorems in inputs:
        source = folder / (module + ".lean")
        imports = set(re.findall(r"^import ([\w.]+)", source.read_text(), re.M))
        if imports & failed:
            print(f"Skipped {module}: missing {sorted(imports & failed)}", flush=True)
            failed.add(module)
            continue
        try:
            build(project, source, module, theorems)
        except subprocess.CalledProcessError:
            failed.add(module)
    if failed:
        raise RuntimeError(f"Incomplete original coefficient checks: {sorted(failed)}")


def main(project, retained_imports):
    BASE["main"](project, original_log=True, retained_imports=retained_imports, continuation=True)
    compile_coefficients(project)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="verified common-pin import archive")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    main(args.project.resolve(), retained)
