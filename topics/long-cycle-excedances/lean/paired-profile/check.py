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
    "FiniteAdjacentResidues",
    "SymmetricPoleComparison",
    "PrincipalAdjacentError",
    "ExactCycleProbabilityLimit",
    "FactorialProbabilityTail",
    "ProbabilityErrorBands",
    "CenteredPrincipalCost",
    "FinitePrincipalCost",
    "WindowPrincipalLimit",
    "RepositoryAdjacentWindows",
    "BinProductMajorant",
    "BinIntegerCertificate",
    "BivariateBin",
    "LiteralBin",
    "LiteralBinSupport",
    "MarkedCoefficientComparison",
    "WeightedMarkedBins",
    "CenteredBinGeometry",
    "CenteredMarkedProduct",
    "BinCostTail",
    "TiltedNumeratorMass",
    "PrincipalRowKernel",
    "LiteralPrincipalTilt",
    "PrincipalBinHeadTail",
    "PrimitiveBinMass",
    "PrimitiveFirstBlock",
    "PrimitiveCheckerMass",
    "DiscreteOddTail",
    "PrimitiveLinearEnvelope",
    "SignedStarEnvelope",
    "PrimitiveBinAssembly",
    "DyadicStarCertificate",
    "LiteralLinearTable",
    "PrimitiveNumeratorInputs",
    "LinearSlabs",
    "RepositoryPrincipalSlab",
    "FiniteWeightedBinCost",
    "NonprincipalPoleValue",
    "NonprincipalValueCost",
    "NonprincipalMoment",
    "RepositoryNonprincipalCost",
    "RegularNumeratorBin",
    "RegularValueCost",
    "RepositoryRegularCost",
    "ScaledMultipleBudget",
    "CutoffAtomGeometry",
    "AtomMultipleBudget",
    "AtomMultipleCost",
    "AtomWindowAggregate",
    "RepositoryMultipleAtom",
    "CutoffSinglePrimitive",
    "CutoffSingleSlabs",
    "RepositoryCutoffJump",
    "PrincipalConjugation",
    "PrincipalPhase",
    "ActualWindowParts",
    "ActualPrincipalPair",
    "ActualNumeratorCost",
    "ActualWindowError",
    "FiniteCarrierError",
    "FourWindowErrors",
    "OriginalDeterminantLimit",
    "RepositoryFourErrorDeterminant",
    "RoundedProductTable",
    "PrincipalCostTable",
    "IntegerCostCertificate",
    "FixedPrincipalCaps",
    "PrincipalCostBridge",
)
EXPECTED = {
    "RepositoryQuotientAudit.slab_margin_budget",
    "RepositoryQuotientAudit.original_determinant_of_ledger_cap",
    "RepositoryQuotientAudit.original_angular_window_limit",
    "RepositoryQuotientAudit.original_four_error_determinant",
    "RepositoryQuotientAudit.original_determinant_margin",
    "OpenMathResearch.LongCycleExcedances.conjugate_pole_denom",
    "OpenMathResearch.LongCycleExcedances.conjugate_primitive",
    "OpenMathResearch.LongCycleExcedances.conjugate_occupied_product",
    "OpenMathResearch.LongCycleExcedances.principal_phase_cancellation",
    "OpenMathResearch.LongCycleExcedances.finite_determinant_parts",
    "OpenMathResearch.LongCycleExcedances.principal_value_exact",
    "OpenMathResearch.LongCycleExcedances.principal_pair_exact",
    "OpenMathResearch.LongCycleExcedances.actual_numerator_mass",
    "OpenMathResearch.LongCycleExcedances.actual_nonprincipal_mass",
    "OpenMathResearch.LongCycleExcedances.finite_determinant_against_row",
    "OpenMathResearch.LongCycleExcedances.finite_scaled_principal_value",
    "OpenMathResearch.LongCycleExcedances.principal_row_discrepancy",
    "OpenMathResearch.LongCycleExcedances.finite_slab_determinant",
    "OpenMathResearch.LongCycleExcedances.limit_slab_determinant",
    "OpenMathResearch.LongCycleExcedances.normalized_determinant_limit",
    "OpenMathResearch.LongCycleExcedances.literal_slab_scaled_linear_envelope_of_spec",
    "OpenMathResearch.LongCycleExcedances.marked_multiple_dominates",
    "OpenMathResearch.LongCycleExcedances.scaled_multiple_budget",
    "OpenMathResearch.LongCycleExcedances.atom_bin_interval",
    "OpenMathResearch.LongCycleExcedances.atom_kernel_on_bin",
    "OpenMathResearch.LongCycleExcedances.atom_angle_scale",
    "OpenMathResearch.LongCycleExcedances.literal_multiple_scaled_bound",
    "OpenMathResearch.LongCycleExcedances.atom_multiple_bin",
    "OpenMathResearch.LongCycleExcedances.rounded_gap_nonnegative",
    "OpenMathResearch.LongCycleExcedances.atom_multiple_one_pole",
    "OpenMathResearch.LongCycleExcedances.multiple_atom_slab_head",
    "OpenMathResearch.LongCycleExcedances.cutoff_single_weight",
    "OpenMathResearch.LongCycleExcedances.single_cutoff_primitive_lattice",
    "OpenMathResearch.LongCycleExcedances.single_cutoff_slab_of_spec",
    "OpenMathResearch.LongCycleExcedances.cutoff_jump_split",
    "OpenMathResearch.LongCycleExcedances.cutoff_jump_head_of_spec",
    "OpenMathResearch.LongCycleExcedances.original_cutoff_jump_head",
    "OpenMathResearch.LongCycleExcedances.regular_numerator_strict_bin",
    "OpenMathResearch.LongCycleExcedances.regular_term_on_bin",
    "OpenMathResearch.LongCycleExcedances.regular_one_pole",
    "OpenMathResearch.LongCycleExcedances.original_regular_numerator_head",
    "OpenMathResearch.LongCycleExcedances.all_pole_zeroth_moment",
    "OpenMathResearch.LongCycleExcedances.regular_bin_lattice",
    "OpenMathResearch.LongCycleExcedances.regular_slab_head_of_spec",
    "OpenMathResearch.LongCycleExcedances.literal_rounded_head_bound",
    "OpenMathResearch.LongCycleExcedances.finite_weighted_bin_cost",
    "OpenMathResearch.LongCycleExcedances.angular_pole_sine_difference",
    "OpenMathResearch.LongCycleExcedances.angular_pole_sine_norm",
    "OpenMathResearch.LongCycleExcedances.value_kernel_on_bin",
    "OpenMathResearch.LongCycleExcedances.value_probability_on_bin",
    "OpenMathResearch.LongCycleExcedances.value_term_on_bin",
    "OpenMathResearch.LongCycleExcedances.nonprincipal_value_one_pole",
    "OpenMathResearch.LongCycleExcedances.finite_nonprincipal_first_moment",
    "OpenMathResearch.LongCycleExcedances.original_nonprincipal_value_head",
    "OpenMathResearch.LongCycleExcedances.nonprincipal_bin_lattice",
    "OpenMathResearch.LongCycleExcedances.nonprincipal_slab_head_of_spec",
    "OpenMathResearch.LongCycleExcedances.rationalPrincipalCost_le_integer_certificate",
    "OpenMathResearch.LongCycleExcedances.fixedPrincipalCaps_ledger",
    "OpenMathResearch.LongCycleExcedances.rationalPrincipalCost_le_fixed_cap",
    "OpenMathResearch.LongCycleExcedances.original_slab_principal_le_fixed_cap",
    "OpenMathResearch.LongCycleExcedances.original_slab_principal_le_computed_cap",
    "OpenMathResearch.LongCycleExcedances.rationalCenteredError_cast",
    "OpenMathResearch.LongCycleExcedances.roundedSlabQ_recurrence",
    "OpenMathResearch.LongCycleExcedances.principalHeadEstimate_le_computed_cap",
    "OpenMathResearch.LongCycleExcedances.rationalPrincipalCost_le_millionths",
    "OpenMathResearch.LongCycleExcedances.qSlabPrefix_get",
    "OpenMathResearch.LongCycleExcedances.qPrefix_get",
    "OpenMathResearch.LongCycleExcedances.roundedQ_step",
    "OpenMathResearch.LongCycleExcedances.original_slab_principal_head_tail",
    "OpenMathResearch.LongCycleExcedances.slab_principal_head_tail_of_spec",
    "OpenMathResearch.LongCycleExcedances.marked_full_nonnegative",
    "OpenMathResearch.LongCycleExcedances.marked_full_degree_support",
    "OpenMathResearch.LongCycleExcedances.reflected_row_majorant",
    "OpenMathResearch.LongCycleExcedances.marked_product_dominates",
    "OpenMathResearch.LongCycleExcedances.marked_product_geometry",
    "OpenMathResearch.LongCycleExcedances.weighted_marked_cost",
    "OpenMathResearch.LongCycleExcedances.centeredBinIndex_valid",
    "OpenMathResearch.LongCycleExcedances.centered_probability_on_bin",
    "OpenMathResearch.LongCycleExcedances.centered_marked_partial",
    "OpenMathResearch.LongCycleExcedances.centered_marked_cost",
    "OpenMathResearch.LongCycleExcedances.cost_split_head_tail",
    "OpenMathResearch.LongCycleExcedances.product_tilt_cost_bound",
    "OpenMathResearch.LongCycleExcedances.symmetric_bin_tail_reserve",
    "OpenMathResearch.LongCycleExcedances.tilted_numerator_mass",
    "OpenMathResearch.LongCycleExcedances.finite_principal_row_kernel",
    "OpenMathResearch.LongCycleExcedances.principal_primitive_norm_majorant",
    "OpenMathResearch.LongCycleExcedances.literal_principal_tilt",
    "OpenMathResearch.LongCycleExcedances.principal_bin_head_tail",
    "OpenMathResearch.LongCycleExcedances.finite_principal_cost",
    "OpenMathResearch.LongCycleExcedances.centered_principal_cost",
    "OpenMathResearch.LongCycleExcedances.off_principal_window_cofinal",
    "OpenMathResearch.LongCycleExcedances.finite_scaled_principal_tends",
    "OpenMathResearch.LongCycleExcedances.determinant_of_window_errors",
    "RepositoryQuotientAudit.original_window_determinant_lower",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_centered_probability_error",
    "OpenMathResearch.LongCycleExcedances.finite_pole_adjacent",
    "OpenMathResearch.LongCycleExcedances.finite_adjacent_occupied_rows",
    "OpenMathResearch.LongCycleExcedances.symmetric_pole_window_cofinal",
    "OpenMathResearch.LongCycleExcedances.symmetric_pole_window_conjugate",
    "OpenMathResearch.LongCycleExcedances.determinant_lower_of_symmetric_windows",
    "OpenMathResearch.LongCycleExcedances.principal_error_hasSum",
    "OpenMathResearch.LongCycleExcedances.principal_error_increment",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.numeratorDiff_hasSum_limit",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.probability_tends_to_harmonic",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.probability_limit_band",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.probability_tail_identity",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.probability_factorial_tail",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.probability_error_bands",
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


def replay_principal_arithmetic(project):
    evaluation_sources = (
        HERE.parent / "sine-comparison" / "EvalLinearTable.lean",
        HERE / "RunPrincipal.lean",
        HERE / "RunCosts.lean",
        HERE / "RunFixedLedger.lean",
    )
    outputs = []
    for original in evaluation_sources:
        source = project / original.name
        shutil.copyfile(original, source)
        print(f"Evaluate {source.name} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
        output = subprocess.check_output(["lake", "env", "lean", str(source)], cwd=project)
        result = project / f"{source.stem}.txt"
        result.write_bytes(output)
        outputs.append(result)
        print(f"Evaluation output-sha256={sha256(output).hexdigest()}", flush=True)
    checker = HERE / "check-principal-cost.py"
    print(f"Independent checker sha256={sha256(checker.read_bytes()).hexdigest()}", flush=True)
    subprocess.run(
        [sys.executable, "-I", str(checker), str(outputs[0]), "--lean-q", str(outputs[1]),
         "--lean-caps", str(outputs[2]), "--lean-ledger", str(outputs[3])],
        check=True,
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
    sine_sources = {
        "BinIntegerCertificate",
        "BinProductMajorant",
        "BivariateBin",
        "DiscreteOddTail",
        "DyadicStarCertificate",
        "LinearSlabs",
        "LiteralBin",
        "LiteralBinSupport",
        "LiteralLinearTable",
        "PrimitiveBinAssembly",
        "PrimitiveBinMass",
        "PrimitiveCheckerMass",
        "PrimitiveFirstBlock",
        "PrimitiveLinearEnvelope",
        "PrimitiveNumeratorInputs",
        "PrimitivePoleKernel",
        "SignedStarEnvelope",
    }
    for name in MODULES:
        directory = HERE.parent / "sine-comparison" if name in sine_sources else HERE
        inputs.append((name, directory / f"{name}.lean"))
    observed = {}
    failed_modules = set()
    for module, original in inputs:
        direct_imports = set(re.findall(r"^import (\w+)$", original.read_text(), re.MULTILINE))
        failed_imports = direct_imports & failed_modules
        if failed_imports:
            failed_modules.add(module)
            print(f"Skip {module} after failed dependencies {sorted(failed_imports)}", flush=True)
            continue
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
        if result.returncode:
            failed_modules.add(module)
            continue
        for name, axioms in AXIOM_REPORT.findall(result.stdout):
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}

    if failed_modules:
        raise RuntimeError(f"Failed or skipped modules: {sorted(failed_modules)}")
    for name in sorted(EXPECTED):
        if name not in observed or observed[name] - common.ALLOWED:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {name}: {observed.get(name)}")
    for module, _ in inputs:
        common.run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    replay_principal_arithmetic(project)
    print(f"PASS: {len(EXPECTED)} paired-profile declarations audited", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
