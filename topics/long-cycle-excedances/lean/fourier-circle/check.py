"""Compile the common-circle lemmas in a fresh module directory and check their axiom reports."""
from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory

SOURCES = Path(__file__).resolve().parent
THEOREMS = {
    "FourierCircleShift": ["shifted_periodic_derivative"],
    "FourierCircleContrast": [
        "fourier_modulation", "fourier_linear_pair", "fourier_kernel_second", "fourier_old_row_twice",
    ],
    "FourierAdjacentIdentity": ["contrast_pole_split", "fourier_adjacent_twice"],
    "FourierPoleMoment": [
        "angular_inverse_square", "circle_inverse_pole", "squared_pole_partial_fractions",
    ],
    "FourierPolePair": ["normalizedPole_second_moment", "normalizedPole_pair_integral"],
    "FourierFinitePoleBound": ["finite_pole_product_bound"],
    "FourierPoleUniform": ["normalizedPole_le_two", "normalizedPole_uniform"],
    "FourierInfinitePoleBound": ["infinite_pole_product_bound"],
    "FourierComplexPoleBound": ["norm_pole_term", "complex_pole_product_bound"],
    "FourierLatticeWeights": ["lattice_inverse_summable", "lattice_eventually_far", "lattice_moment_weights"],
    "FourierPoleContrast": ["normalized_lattice_contrast"],
    "FourierOddPoleProduct": ["odd_lattice_pole_product"],
    "FourierRowPoleProduct": ["row_circle_pole_product"],
    "FourierSquaredSum": ["infinite_squared_pole_integral"],
    "FourierPoleDifferentiation": ["norm_squared_pole_term", "complexPoleKernel_angular_deriv"],
    "FourierDerivativeBound": ["complexPoleKernel_derivative_bound"],
    "FourierLogarithmicGap": [
        "exponential_period_gap", "odd_logistic_denominator_gap",
        "odd_logistic_contraction", "original_contracted_circle_ratio",
    ],
    "FourierExponentialGap": [
        "exp_principal_denominator", "uniform_principal_denominator", "original_principal_denominator",
    ],
    "FourierCircleChoice": [
        "two_candidate_gap", "original_odd_circle_choice", "original_odd_circle_modulus_gap",
    ],
    "FourierOriginalDenominators": ["original_circle_uniform_denominators"],
    "FourierLatticeDerivative": [
        "odd_lattice_contrast_first_moment", "lattice_squared_weights", "odd_lattice_contrast_derivative",
    ],
    "FourierNormComparison": [
        "fourier_old_coefficient_bound", "fourier_adjacent_coefficient_bound", "fourier_kernel_error",
    ],
    "FourierLatticeSplit": [
        "odd_lattice_contrast_split", "circle_contrast_sum",
    ],
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'OpenMathResearch\.LongCycleExcedances\.(\w+)' depends on axioms:\s*\[([^\]]*)\]")


def main():
    print(subprocess.check_output(["lean", "--version"], text=True).strip(), flush=True)
    with TemporaryDirectory() as temporary:
        path = Path(temporary)
        env = dict(os.environ)
        # Lake can supply relative paths. Resolve them before changing the compiler's working directory.
        imports = [str(Path(item).resolve()) for item in env.get("LEAN_PATH", "").split(os.pathsep) if item]
        env["LEAN_PATH"] = os.pathsep.join([temporary, *imports])
        for module, names in THEOREMS.items():
            source = shutil.copyfile(SOURCES / f"{module}.lean", path / f"{module}.lean")
            print(f"Compile {module} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
            run = subprocess.run(
                ["lean", "-o", f"{module}.olean", source.name], cwd=path, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            print(run.stdout, end="", flush=True)
            run.check_returncode()
            reports = dict(REPORT.findall(run.stdout))
            if set(reports) != set(names):
                raise ValueError(f"Unexpected declaration reports for {module}: {sorted(reports)}")
            for name, listed in reports.items():
                axioms = {entry.strip() for entry in listed.split(",") if entry.strip()}
                if axioms - ALLOWED:
                    raise ValueError(f"{name} uses additional axioms: {sorted(axioms - ALLOWED)}")
    print(f"PASS: {sum(map(len, THEOREMS.values()))} declared theorem audits", flush=True)


if __name__ == "__main__":
    main()
