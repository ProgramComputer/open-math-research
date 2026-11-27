#!/usr/bin/env python3
"""Check enclosed Fourier residue budgets against the authenticated common pin."""
import argparse
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
HIGH = runpy.run_path(str(HERE.parent / "fourier-high-height" / "check.py"))
STABLE = HIGH["STABLE"]
VERTICAL = (
    "UnimodalMesh", "GammaDensity", "GammaPeak", "AllCutoffMesh",
    "VerticalTransport", "VerticalRadius", "VerticalMeshSum", "PoleModeIdentity",
    "PoleChord", "ComplexDiscreteMoment", "RepositoryLogTiltDiscrete",
)
WIDE = (
    "WideDensity", "WideGeometry", "WideOddMass", "WideOddRadius",
    "WideVerticalTransport", "WidePoleChord", "RepositoryWideResidues",
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
    support("uniform-log-tilt", "UniformDiscreteTilt")
    for module in VERTICAL:
        support("vertical-tilt", module)
    count = 0
    for module in WIDE:
        namespace = HIGH["ORIGINAL"] if module == "RepositoryWideResidues" else HIGH["GENERIC"]
        count += HIGH["check_module"](project, HERE / (module + ".lean"), namespace)
    print(f"PASS: {count} enclosed Fourier residue declarations audited", flush=True)


if __name__ == "__main__":
    main()
