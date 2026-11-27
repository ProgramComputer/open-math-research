#!/usr/bin/env python3
"""Check the paired-residue profile bridge using the shared research pin."""

import importlib.util
import re
import shutil
import subprocess
import sys
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
TOPIC = HERE.parents[1]
SUPPORT = (
    ("lean/sine-comparison", "PrincipalDisk"),
    ("lean/sine-comparison", "PrincipalIntegral"),
    ("lean/sine-comparison", "PrincipalFactor"),
    ("color-acceptance", "ColorAnchor"),
    ("color-acceptance", "ColorPermSplit"),
    ("color-acceptance", "ColorBlock"),
    ("color-acceptance", "ColorCycleCount"),
    ("color-acceptance", "ColorSupportCount"),
    ("color-load-bounds", "MarkedColorLoads"),
    ("lean/probability-bands", "CycleProbabilityBands"),
    ("lean/probability-bands", "AnchoredProbability"),
    ("lean/probability-bands", "RepositoryProbabilityBands"),
    ("color-load-bounds", "RepositoryOrbitBaseline"),
)
MODULES = (
    "FinitePoleProduct",
    "PairedPoleFamily",
    "PairedPoleConvergence",
    "PairedCycleNormalization",
    "PairedCoefficientLimit",
    "ScaledCycleProfile",
    "RepositoryPairedCycleLift",
    "RepositoryScaledCycleProfile",
    "CutoffFormalExp",
    "ExpAdd",
    "PairedExpProduct",
    "RepositoryPairedProductLimit",
    "OccupiedSupportNet",
    "OccupiedCoefficient",
    "OccupiedExpansion",
    "ActualOccupiedValue",
    "ActualOccupiedLimit",
    "OccupiedTuple",
    "RepositoryOccupiedValue",
    "CycleNumeratorVariation",
    "CutoffCycleSeriesRecurrence",
    "RepositoryNumeratorVariation",
    "EntireCycleEvaluation",
    "RepositoryPrincipalFactor",
    "PrincipalLatticeProduct",
    "PrimitivePoleKernel",
    "ReflectedLogTail",
    "ReflectedLogSum",
    "ReflectedLogBudget",
    "PrincipalBudgetJoin",
    "PrincipalHarmonic",
    "PrincipalScaledBudget",
)
EXPECTED = {
    "OpenMathResearch.LongCycleExcedances.primitive_angular_bernoulli_kernel",
    "OpenMathResearch.LongCycleExcedances.reflected_log_all",
    "OpenMathResearch.LongCycleExcedances.reflected_log_bound_of_pair",
    "OpenMathResearch.LongCycleExcedances.reflected_log_low_budget",
    "OpenMathResearch.LongCycleExcedances.reflected_log_all_budget",
    "OpenMathResearch.LongCycleExcedances.actual_principal_real_bound_all",
    "OpenMathResearch.LongCycleExcedances.actual_principal_real_bound_low",
    "OpenMathResearch.LongCycleExcedances.principal_harmonic_prefactor",
    "OpenMathResearch.LongCycleExcedances.original_scaled_principal_all",
    "OpenMathResearch.LongCycleExcedances.original_scaled_principal_low",
    "OpenMathResearch.LongCycleExcedances.principal_pole_ratio_norm_le",
    "OpenMathResearch.LongCycleExcedances.principal_log_lattice_summable",
    "OpenMathResearch.LongCycleExcedances.principal_lattice_factors_hasProd",
    "OpenMathResearch.LongCycleExcedances.principal_log_lattice_single_bound",
    "OpenMathResearch.LongCycleExcedances.principal_product_re_of_lattice_majorant",
    "OpenMathResearch.LongCycleExcedances.principal_disk_exp_re",
    "OpenMathResearch.LongCycleExcedances.principal_radial_denominator",
    "OpenMathResearch.LongCycleExcedances.principal_log_integral_bound",
    "OpenMathResearch.LongCycleExcedances.principal_log_integral_eq",
    "OpenMathResearch.LongCycleExcedances.principal_exp_integral_eq_factor",
    "OpenMathResearch.LongCycleExcedances.principal_lagrange_factor_eq_exp",
    "OpenMathResearch.LongCycleExcedances.cutoff_numerator_hasSum",
    "OpenMathResearch.LongCycleExcedances.original_numerator_hasSum",
    "OpenMathResearch.LongCycleExcedances.occupied_primitive_hasSum",
    "OpenMathResearch.LongCycleExcedances.occupied_factor_hasSum_integral",
    "OpenMathResearch.LongCycleExcedances.occupied_product_hasSum_integral",
    "OpenMathResearch.LongCycleExcedances.finite_pole_partition",
    "OpenMathResearch.LongCycleExcedances.finite_distinguished_pole_product",
    "OpenMathResearch.LongCycleExcedances.finite_pole_product_resummed",
    "OpenMathResearch.LongCycleExcedances.finite_cycle_series_poles",
    "OpenMathResearch.LongCycleExcedances.finite_cycle_primitive_coeff",
    "OpenMathResearch.LongCycleExcedances.pairedPoleDenom_sub",
    "OpenMathResearch.LongCycleExcedances.finite_paired_cycle_series",
    "OpenMathResearch.LongCycleExcedances.finite_paired_cycle_coeff",
    "OpenMathResearch.LongCycleExcedances.summable_paired_pole_power_norm",
    "OpenMathResearch.LongCycleExcedances.summable_paired_pole_first_moment",
    "OpenMathResearch.LongCycleExcedances.hasSum_paired_cycle_log_coeff",
    "OpenMathResearch.LongCycleExcedances.paired_scaled_odd_sum",
    "OpenMathResearch.LongCycleExcedances.paired_single_cycle_normalization",
    "OpenMathResearch.LongCycleExcedances.tendsto_truncated_exp_coeff",
    "OpenMathResearch.LongCycleExcedances.tendsto_paired_log_power_coeff",
    "OpenMathResearch.LongCycleExcedances.tendsto_power_coeff_of_tendsto_coeff",
    "OpenMathResearch.LongCycleExcedances.truncated_exp_eq_scaled_profile_sum",
    "OpenMathResearch.LongCycleExcedances.coeff_pow_eq_scaled_ordered_profile",
    "RepositoryQuotientAudit.original_paired_single_cycle_coeff",
    "RepositoryQuotientAudit.original_hasSum_paired_cycle_log_coeff",
    "RepositoryQuotientAudit.original_scaled_cycle_profile_exp",
    "RepositoryQuotientAudit.tendsto_original_scaled_cycle_profile_exp",
    "OpenMathResearch.LongCycleExcedances.coeff_cutoffExp",
    "OpenMathResearch.LongCycleExcedances.cutoffExp_add",
    "OpenMathResearch.LongCycleExcedances.finite_paired_product_coeff_below_cutoff",
    "OpenMathResearch.LongCycleExcedances.cutoffExp_rescale",
    "OpenMathResearch.LongCycleExcedances.finite_paired_product_eq_truncated_exp",
    "RepositoryQuotientAudit.tendsto_original_scaled_finite_paired_products",
    "OpenMathResearch.LongCycleExcedances.hasSum_comp_finite_support",
    "OpenMathResearch.LongCycleExcedances.summable_occupied_finset",
    "OpenMathResearch.LongCycleExcedances.summable_occupiedCoeff",
    "OpenMathResearch.LongCycleExcedances.finite_occupiedCoeff_sum",
    "OpenMathResearch.LongCycleExcedances.tendsto_occupiedCoeff_sum",
    "OpenMathResearch.LongCycleExcedances.summable_actual_occupiedCoeff",
    "OpenMathResearch.LongCycleExcedances.finite_actual_occupiedCoeff",
    "OpenMathResearch.LongCycleExcedances.actual_occupiedCoeff_eq_of_product_limit",
    "OpenMathResearch.LongCycleExcedances.occupiedCoeff_eq_sorted_tuple",
    "RepositoryQuotientAudit.original_scaled_occupied_value",
    "OpenMathResearch.LongCycleExcedances.cutoffCycleSeries_coeff_recurrence",
    "OpenMathResearch.LongCycleExcedances.coeff_cutoffCycleSeries_eq_of_spec",
    "OpenMathResearch.LongCycleExcedances.coeff_cutoffCycleNumerator_eq_of_spec",
} | {
    "OpenMathResearch.LongCycleExcedances.CycleProbability." + name
    for name in (
        "originalProbability_spec",
        "Spec.reciprocal_bounds",
        "Spec.numeratorDiff_at_cutoff",
        "Spec.numeratorDiff_between",
        "Spec.numeratorDiff_at_twice",
        "Spec.numeratorDiff_at_twice_pos_lt",
        "Spec.mul_numeratorDiff_eq_neg_sum",
        "Spec.first_block_variation",
        "Spec.numeratorDiff_factorial_block",
        "coeff_cutoffCycleSeries_eq_originalProbability",
        "coeff_cutoffCycleNumerator_eq_original",
        "originalNumeratorCoeff_at_cutoff",
        "originalNumeratorCoeff_between",
        "originalNumeratorCoeff_at_twice",
        "originalNumeratorCoeff_at_twice_pos_lt",
        "originalNumeratorCoeff_first_block_variation",
        "originalNumeratorCoeff_factorial_block",
    )
}
AXIOM_REPORT = re.compile(
    r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
    re.MULTILINE,
)


def main(project, imports):
    spec = importlib.util.spec_from_file_location(
        "common_pin", HERE.parent / "common-pin" / "check.py"
    )
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    project.mkdir(parents=True)
    common.prepare(project)
    version = common.run(project, "lean", "--version", capture=True).strip()
    if common.COMPILER not in version:
        raise ValueError(f"unexpected compiler {version}")
    print(version, flush=True)
    common.run(project, "lake", "exe", "cache", "get")
    mathlib = common.run(
        project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD", capture=True
    ).strip()
    if mathlib != common.MATHLIB:
        raise ValueError(f"unexpected mathlib {mathlib}")
    print(f"mathlib {mathlib}", flush=True)

    if imports is None:
        common.run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient")
    else:
        digest = sha256(imports.read_bytes()).hexdigest()
        if digest != common.IMPORT_SHA:
            raise ValueError(f"unexpected retained object archive {digest}")
        common.run(project, "tar", "--zstd", "-xf", str(imports))
        print(f"Reused verified common-pin archive sha256={digest}", flush=True)

    inputs = [(name, TOPIC / folder / f"{name}.lean") for folder, name in SUPPORT]
    inputs.extend((name, (HERE.parent / "sine-comparison" if name == "PrimitivePoleKernel" else HERE) / f"{name}.lean") for name in MODULES)
    observed = {}
    for module, original in inputs:
        source = project / original.name
        shutil.copyfile(original, source)
        output = project / ".lake" / "build" / "lib" / "lean" / (module + ".olean")
        print(f"Compile {module} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", "-o", str(output), str(source)],
            cwd=project,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="", flush=True)
        result.check_returncode()
        for name, axioms in AXIOM_REPORT.findall(result.stdout):
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}

    for name in sorted(EXPECTED):
        if name not in observed or observed[name] - common.ALLOWED:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {name}: {observed.get(name)}")
    for module, _ in inputs:
        common.run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(EXPECTED)} paired-profile declarations audited", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
