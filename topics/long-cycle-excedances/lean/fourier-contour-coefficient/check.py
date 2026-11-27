#!/usr/bin/env python3
"""Build and audit the original permutation coefficient contour identity."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy
import subprocess
import shutil

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


def stage_fourier_shift(project):
    """Apply the #318 compatibility proof only to its known pre-port source."""
    folder = project / "contour-inputs"
    folder.mkdir()
    source = HERE.parent / "fourier-circle" / "FourierCircleShift.lean"
    target = folder / source.name
    shutil.copyfile(source, target)
    raw = sha256(target.read_bytes()).hexdigest()
    print(f"FourierCircleShift raw-sha256={raw}", flush=True)
    if raw == "2aa40e1273e13dbfba41ef771a33927fa9da8324f0167fb4bf723e7e4aeb2cee":
        subprocess.run(["patch", "--batch", str(target),
                        str(HERE / "FourierCircleShift.common-pin.patch")], check=True)
    expected = "5d8db3cd4b1c3f3e3ad92e512b33033387c4de01dfeb7c89b35428e694ff8c80"
    if sha256(target.read_bytes()).hexdigest() != expected:
        raise ValueError("Unexpected FourierCircleShift production input")
    STABLE["build_local"](project, target, "FourierCircleShift", ())


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
    stage_fourier_shift(project)
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
