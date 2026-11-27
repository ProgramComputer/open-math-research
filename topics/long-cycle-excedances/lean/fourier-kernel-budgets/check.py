"""Replay the numerical kernel bounds on the original Fourier dependencies."""
import argparse
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))
MANIFEST = (
    ("FourierPolePointwiseBudget", ("row_pole_coefficient_bound", "squared_gap_inverse_factors")),
    ("FourierLiteralKernelBudgets", ("literal_fourier_kernel_budgets",)),
)


def compile_kernel_budgets(project):
    """Compile the two new modules in a project with the coefficient and moment inputs."""
    build = BASE["build_local"]
    for module, theorems in MANIFEST:
        build(project, HERE / f"{module}.lean", module, theorems)
    print("PASS: two kernel-budget modules and three new declaration audits", flush=True)


def main(project, retained_imports):
    coefficients = runpy.run_path(str(HERE.parent / "fourier-stable/check-original-coefficients.py"))
    moments = runpy.run_path(str(HERE.parent / "fourier-odd-moments/check.py"))
    coefficients["main"](project, retained_imports)
    moments["compile_moments"](project)
    compile_kernel_budgets(project)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin import archive")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    main(args.project.resolve(), retained)
