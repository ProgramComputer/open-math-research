"""Replay the original minor-residue bounds for cutoffs eight through ninety-nine."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = (
    "SmallResidueGeometry", "SmallResidueDensity", "SmallResidueChord",
    "SmallResidueRadius", "SmallResidueMass", "RepositorySmallCutoffResidues",
    "RepositorySmallMinorSums",
)


def compile_small_residues(project):
    high = runpy.run_path(str(HERE.parent / "fourier-high-height/check.py"))
    failures = []
    for module in MODULES:
        namespace = high["ORIGINAL"] if module.startswith("Repository") else high["GENERIC"]
        try:
            high["check_module"](project, HERE / (module + ".lean"), namespace)
        except (subprocess.CalledProcessError, ValueError):
            failures.append(module)
    if failures:
        raise RuntimeError(f"Incomplete small-cutoff checks: {failures}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-minor-sums/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    compile_small_residues(project)
