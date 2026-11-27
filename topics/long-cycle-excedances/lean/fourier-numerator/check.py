"""Replay the small-height cutoff proof on the common Lean pin."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy
import shutil
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
FOURIER = HERE.parent / "fourier-circle"
REAL_AXIS = runpy.run_path(str(HERE.parent / "fourier-stable" / "check-real-axis.py"))
REPORTS = runpy.run_path(str(FOURIER / "check.py"))["THEOREMS"]
NUMERATOR = (
    "NumeratorPoleVolume",
    "NumeratorLogDefinitions",
    "NumeratorOddPoleMoment",
    "NumeratorRadialScalars",
    "NumeratorTaylorContraction",
    "NumeratorLogSeries",
)
ADAPTER = (
    "numerator_log_coeff_eq_original",
    "numerator_taylor_eq_original",
    "numerator_original_cutoff_series_contraction",
)


def compile_numerator(project):
    build = REAL_AXIS["build_local"]
    with TemporaryDirectory() as directory:
        staging = Path(directory)
        for module in NUMERATOR:
            source = FOURIER / f"{module}.lean"
            target = staging / source.name
            shutil.copyfile(source, target)
            patch = HERE / "ports" / f"{module}.patch"
            source_hash = sha256(source.read_bytes()).hexdigest()
            if patch.exists():
                data = patch.read_bytes()
                print(f"Prepare {module} source-sha256={source_hash} "
                      f"patch-sha256={sha256(data).hexdigest()}", flush=True)
                subprocess.run(
                    ["patch", "--batch", "--silent", "--fuzz=0", "-p0"],
                    input=data, cwd=staging, check=True,
                )
            else:
                print(f"Prepare {module} source-sha256={source_hash}", flush=True)
            build(project, target, module, REPORTS[module])
    build(project, HERE / "NumeratorCutoffAdapter.lean", "NumeratorCutoffAdapter", ADAPTER)
    print(f"PASS: {len(NUMERATOR)+1} numerator modules and "
          f"{sum(len(REPORTS[m]) for m in NUMERATOR)+len(ADAPTER)} numerator declaration audits")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin import archive")
    args = parser.parse_args()
    project = args.project.resolve()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    REAL_AXIS["main"](project, True, retained)
    compile_numerator(project)
