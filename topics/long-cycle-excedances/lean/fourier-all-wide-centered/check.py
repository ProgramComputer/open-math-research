"""Check the centered old and adjacent original rows at every eligible cutoff."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def compile_all_wide_centered(project):
    for path, stage in (
        ("fourier-small-residues", "compile_small_residues"),
        ("fourier-small-boundary", "compile_small_boundary"),
    ):
        runpy.run_path(str(HERE.parent / path / "check.py"))[stage](project)
    high = runpy.run_path(str(HERE.parent / "fourier-high-height/check.py"))
    high["check_module"](project, HERE / "RepositoryAllWideCenteredRows.lean", high["ORIGINAL"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-centered/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    compile_all_wide_centered(project)
