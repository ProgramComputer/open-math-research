"""Replay the numerical kernel bounds on the original Fourier dependencies."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy
from tempfile import TemporaryDirectory
from urllib.request import urlopen

HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))
MANIFEST = (
    ("FourierPolePointwiseBudget", ("row_pole_coefficient_bound", "squared_gap_inverse_factors")),
    ("FourierLiteralKernelBudgets", ("literal_fourier_kernel_budgets",)),
)

CIRCLE_PATH = Path("topics/long-cycle-excedances/lean/fourier-circle")
CIRCLE_COMMIT = "ade4acc68e05cf882f3733308e18b61477a381d4"
CIRCLE_INPUTS = (
    ("FourierPoleMoment", "23bf322befb2e9523231c5a541c9689f0ea0753314a99262171c5ff0354b9113"),
    ("FourierPolePair", "b2bbbb31898fe9aa787b58109945f5f29e46de8227fc20705ef0a61725e057fe"),
    ("FourierFinitePoleBound", "d8291164c18dd4d573803cb26e29b2b6280abee2099ae72dc72260171d862ed6"),
    ("FourierPoleUniform", "897d2ef846db5c4122f6ad0c77cd0661ca7bea7178a9285528506c929eb4f2ba"),
    ("FourierInfinitePoleBound", "2783b2df55f4f82a7d3f7e79902304d881f96c9f278960e94665cb8aa0fee989"),
    ("FourierComplexPoleBound", "ddfca50f7a5436bbec30813662a0163317f661e1d4359bec4d61605459d8dd45"),
    ("FourierSquaredSum", "5e91d5832b19018d9fd4ecf3ff7c1aeb18363ad5adbd40babbbec8f491b5d3d8"),
    ("FourierPoleDifferentiation", "c9341f4e23d1e4d54a37f56d3607b963a80999aee2b90e1e7b3d0a233b0614e1"),
    ("FourierLatticeWeights", "e614c64b70c2abe9c59d69090f48900bc620cae5606528789e8f33af28f116fb"),
)


def compile_kernel_budgets(project):
    """Compile the two new modules in a project with the coefficient and moment inputs."""
    build = BASE["build_local"]
    for module, theorems in MANIFEST:
        build(project, HERE / f"{module}.lean", module, theorems)
    print("PASS: two kernel-budget modules and three new declaration audits", flush=True)


def compile_kernel_imports(project):
    root = HERE.parents[3]
    build = BASE["build_local"]
    with TemporaryDirectory() as directory:
        for module, expected in CIRCLE_INPUTS:
            relative = CIRCLE_PATH / f"{module}.lean"
            source = root / relative
            data = source.read_bytes() if source.is_file() else b""
            if sha256(data).hexdigest() != expected:
                url = ("https://raw.githubusercontent.com/ProgramComputer/open-math-research/"
                       f"{CIRCLE_COMMIT}/{relative}")
                with urlopen(url, timeout=45) as response:
                    data = response.read()
            if sha256(data).hexdigest() != expected:
                raise ValueError(f"Unexpected input hash for {module} at {CIRCLE_COMMIT}")
            staged = Path(directory) / source.name
            staged.write_bytes(data)
            build(project, staged, module, ())


def main(project, retained_imports):
    BASE["main"](project, original_log=True, retained_imports=retained_imports, continuation=True)
    compile_kernel_imports(project)
    moments = runpy.run_path(str(HERE.parent / "fourier-odd-moments/check.py"))
    moments["compile_moments"](project)
    compile_kernel_budgets(project)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin import archive")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    main(args.project.resolve(), retained)
