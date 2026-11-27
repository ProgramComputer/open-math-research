"""Replay the two normalized nonprincipal residue sums on the shared research pin."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = (
    ("FourierMinorSum", ("empty_minor_window", "normalized_minor_residue_sums",
                         "paired_fourier_error_margin", "paired_fourier_sign_at_zero")),
    ("FourierMinorGeometry", ("minor_window_at_zero", "principal_radius_le_minor")),
    ("LiteralMinorSums", ("literal_minor_sums_of_positive_budgets",)),
)


def compile_minor_sums(project):
    enclosed = runpy.run_path(str(HERE.parent / "fourier-enclosed-residues/check.py"))
    high = enclosed["HIGH"]
    build = enclosed["STABLE"]["build_local"]
    high["check_module"](project, HERE.parent / "middle-residues/NeighborPoleGeometry.lean", high["GENERIC"])
    for module, names in MODULES:
        build(project, HERE / (module + ".lean"), module, names)
    high["check_module"](project, HERE / "RepositoryFourierMinorSums.lean", high["ORIGINAL"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="fresh build directory")
    parser.add_argument("--retained-imports", type=Path, help="authenticated upstream archive")
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-enclosed-residues/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    moments = runpy.run_path(str(HERE.parent / "fourier-odd-moments/check.py"))
    moments["compile_moments"](project)
    compile_minor_sums(project)
