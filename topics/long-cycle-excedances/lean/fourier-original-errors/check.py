"""Rebuild both normalized boundary errors for the original permutation trace."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a fresh build directory")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin objects")
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-amplitude/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    for path, step in (
        ("fourier-stable/check-original-coefficients.py", "compile_coefficients"),
        ("fourier-odd-moments/check.py", "compile_moments"),
        ("fourier-kernel-budgets/check.py", "compile_kernel_budgets"),
        ("fourier-errors/check.py", "compile_errors"),
    ):
        runpy.run_path(str(HERE.parent / path))[step](project)
    build = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))["build_local"]
    build(project, HERE / "FourierOriginalErrorPair.lean", "FourierOriginalErrorPair",
          ("original_normalized_fourier_errors",))


if __name__ == "__main__":
    main()
