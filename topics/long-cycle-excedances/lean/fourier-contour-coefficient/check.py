#!/usr/bin/env python3
"""Build and audit the original permutation coefficient contour identity."""
import argparse
from pathlib import Path
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
HIGH = runpy.run_path(str(HERE.parent / "fourier-high-height" / "check.py"))
STABLE = HIGH["STABLE"]
ANALYTIC = (
    "FourierRealContinuation", "FourierLogisticPoles", "FourierLocalPoleBounds",
    "FourierResolventDerivative", "FourierAnchoredLogistic",
)
MODULES = (
    "SimplePoleRemoval", "AnnularPrincipalParts", "TaylorCircle", "LogisticContour",
    "AdjacentContour", "AnchoredPoleTaylor", "ScalarLogisticTaylor",
    "RepositoryContourCoefficient",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    imports = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    STABLE["main"](project, True, imports)

    def support(folder, module):
        STABLE["build_local"](project, HERE.parent / folder / (module + ".lean"), module, ())

    support("common-pin", "TiltAnalyticEvaluation")
    support("fourier-circle", "FourierCircleShift")
    for module in ANALYTIC:
        support("fourier-stable", module)
    count = 0
    failed = set()
    for module in MODULES:
        source = HERE / (module + ".lean")
        inputs = {line.split()[1] for line in source.read_text().splitlines()
                  if line.startswith("import ")}
        if inputs & failed:
            print(f"Skip {module} because its imports failed: {sorted(inputs & failed)}", flush=True)
            failed.add(module)
            continue
        namespace = HIGH["ORIGINAL"] if module == "RepositoryContourCoefficient" else HIGH["GENERIC"]
        try:
            count += HIGH["check_module"](project, source, namespace)
        except (subprocess.CalledProcessError, ValueError):
            failed.add(module)
    if failed:
        raise RuntimeError(f"Incomplete contour checks: {sorted(failed)}")
    print(f"PASS: {count} contour coefficient declarations audited", flush=True)


if __name__ == "__main__":
    main()
