"""Check the direct Cauchy bounds for the original two permutation rows."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = (
    "SmallCutoffCircleDecay", "SmallCutoffCircle", "SmallCutoffAmplitude",
    "SmallCutoffCauchyPair",
)


def compile_small_boundary(project):
    high = runpy.run_path(str(HERE.parent / "fourier-high-height/check.py"))
    for module in MODULES:
        high["check_module"](project, HERE / (module + ".lean"), high["GENERIC"])
    for path, stage in (
        ("fourier-small-cutoff-numerator", "compile_small_cutoff_numerator"),
        ("fourier-eight-nine", "compile_eight_nine_numerator"),
    ):
        runpy.run_path(str(HERE.parent / path / "check.py"))[stage](project)
    high["check_module"](project, HERE / "RepositorySmallBoundary.lean", high["GENERIC"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-amplitude/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    runpy.run_path(str(HERE.parent / "fourier-stable/check-original-coefficients.py"))["compile_coefficients"](project)
    compile_small_boundary(project)
