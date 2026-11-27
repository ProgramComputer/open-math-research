"""Build the uniform Fourier error reduction on the shared research pin."""
import argparse
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
DRIVER = runpy.run_path(str(HERE.parent / "fourier-stable" / "check-real-axis.py"))
MODULES = (
    ("FourierUniformDecay", ("selected_circle_decay", "uniform_fourier_endpoint",
                             "uniform_normalized_fourier_error")),
    ("FourierKernelScalars", ("scaled_fourier_kernel_bounds",)),
    ("FourierAdjacentBudget", ("absorb_adjacent_fourier_corrections",)),
    ("FourierNormalizedError", ("normalized_circle_error",)),
    ("FourierNumericCoefficients", ("numerical_fourier_coefficient_pair", "correction_bounds_from_entrance")),
    ("FourierCoefficientSpecialization", ("normalized_fourier_pair_of_kernel_masses",)),
)


def compile_errors(project):
    (project / ".lake/build/lib/lean").mkdir(parents=True, exist_ok=True)
    for module, names in MODULES:
        DRIVER["build_local"](project, HERE / f"{module}.lean", module, names)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a fresh directory")
    project = parser.parse_args().project.resolve()
    project.mkdir(parents=True)
    common = DRIVER["COMMON"]
    common["prepare"](project)
    run = common["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if common["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    run(project, "lake", "exe", "cache", "get",
        "Mathlib.Analysis.SpecialFunctions.Log.Deriv", "Mathlib.Tactic.Positivity",
        "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.FieldSimp",
        "Mathlib.Analysis.Complex.Basic")
    for package in json.loads((project / "lake-manifest.json").read_text())["packages"]:
        rev = run(project, "git", "-C", ".lake/packages/" + package["name"],
                  "rev-parse", "HEAD", capture=True).strip()
        if rev != package["rev"]:
            raise ValueError(f"Wrong {package['name']} revision {rev}")
        print(f"{package['name']} {rev}", flush=True)
    compile_errors(project)
