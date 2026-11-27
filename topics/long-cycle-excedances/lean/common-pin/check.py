#!/usr/bin/env python3
"""Check the actual rational endpoint theorem in the frozen Lean environment."""

import io
import re
import runpy
import shutil
import subprocess
import sys
import urllib.request
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile


HERE = Path(__file__).resolve().parent
TOPIC = HERE.parent
REPO = HERE.parents[3]
SHARED = REPO / "shared/lean"
COEFFICIENTS = TOPIC / "pinned-quotient"
IMPORT_SHA = "000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
COMPILER = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
LOGISTIC_IMPORTS = (
    "MarkedTwoCycles", "MarkedTwoEGF", "MarkedExponentialBias", "MarkedLabelBias",
    "MarkedLogistic", "CycleProfile", "CycleProfileEGF", "CycleProfileLogistic",
)
PHASE_MODULES = ("TiltDerivative", "SeventhMoment", "GridSigns", "ActualPhaseDerivative",
                 "PhaseRemainder", "PhasePoleGeometry", "AngularGeometry", "CellReadout",
                 "Displacement", "OriginalAngularCell", "AngularDerivative", "OriginalAngularDerivative",
                 "PhaseMiddle", "MiddleAssembly", "CellRootSelection", "OriginalRootCount")
UNIFORM_MODULES = (
    "UniformDiscreteTilt",
    "LowMomentMass",
    "RadiusGeometry",
    "LowMomentInput",
    "UniformMassSum",
    "LinearTilt",
    "PoleMonomial",
    "UniformHighDegreeLattice",
    "UniformHighDegreeOddPoles",
    "RepositoryUniformHighDegree",
    "RepositoryUniformMass",
)
VERTICAL_MODULES = (
    "UnimodalMesh",
    "GammaDensity",
    "GammaPeak",
    "AllCutoffMesh",
    "VerticalTransport",
    "VerticalRadius",
    "VerticalMeshSum",
    "PoleModeIdentity",
    "PoleChord",
    "ComplexDiscreteMoment",
    "RepositoryLogTiltDiscrete",
    "RepositoryPoleTransport",
    "MinorPoleMass",
    "MinorPoleRadius",
    "RepositoryMinorPoles",
    "SmallRadius",
    "AllAngleMinorPoles",
)
MIDDLE_MODULES = (
    "NestedPoleRadii",
    "NestedPoleLattice",
    "NestedSize",
    "NestedNormalized",
    "NeighborPoleGeometry",
    "ExactPhaseCell",
    "PolePhaseReadout",
    "RepositoryNestedRow",
    "RepositoryEnclosedHalf",
    "CenteredPoleReadout",
    "RepositoryCenteredRows",
    "RepositoryMiddleCells",
)
JOIN_MODULES = (
    "FrontModulusJoin",
    "FrontMiddleWitnesses",
    "JoinAngle",
    "RepositoryJoinAngle",
    "MiddleLevelSelection",
    "RepositoryMiddleLevelSelection",
    "RealFront",
    "OriginalLiteralHalfRoots",
    "RepositoryExteriorReduction",
    "FrontCoefficientNorm",
    "CoefficientFrontWindow",
    "PolynomialFront",
    "RepositoryPolynomialFront",
    "RepositoryExteriorCertificates",
)
COLOR_MODULES = (
    "EulerianColorKernel",
    "ColorAcceptanceSeries",
    "ColorTransformError",
    "RepositoryColorTransform",
    "ColorAnchor",
    "ColorPermSplit",
    "ColorCycleCount",
    "ColorBlock",
    "ColorSupportCount",
    "ColorDoubleCount",
    "ColorRelabel",
    "ColorRecurrence",
    "NormalizedColorRecurrence",
    "NormalizedColorBounds",
    "RepositoryColorCombinatorial",
    "ColorInsertion",
    "RepositoryColorInsertion",
)
BAND_MODULES = ("CycleProbabilityBands", "AnchoredProbability", "RepositoryProbabilityBands")
LOAD_MODULES = (
    "BinomialColorLoad",
    "LoadEnvelope",
    "MarkedColorLoads",
    "MarkedLoadProbability",
    "ColorLoadRanges",
    "CutoffAcceptanceBudget",
    "ColorLagGrid",
    "SparseLagBudget",
    "RepositoryLoadLag",
    "RepositoryOrbitBaseline",
    "RepositoryColorAlpha",
    "FiniteUnimodalMesh",
    "BernsteinProbability",
    "BinomialGridMesh",
    "BinomialPeakAdapter",
    "ColorLoadGrid",
    "RepositoryBinomialGrid",
    "SmallLagGrid",
    "UniformLagBudget",
    "RepositoryUniformLag",
    "FrontLagNormalization",
    "RepositoryExteriorLag",
)
EXPECTED = {
    "OpenMathResearch.LongCycleExcedances.front_rank_square",
    "OpenMathResearch.LongCycleExcedances.front_sparse_of_large_size",
    "OpenMathResearch.LongCycleExcedances.front_remove_lag_normalization",
    "RepositoryQuotientAudit.original_global_lag_bound",
    "RepositoryQuotientAudit.original_exterior_near_lag",

    "OpenMathResearch.LongCycleExcedances.ColorAnchor.accepted_probability_eq_realCount",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.baselinePairs_card",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.baselinePairs_probability",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.baselinePairs_probability_bounds",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.orbitSize_eq_lengthAt",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.originalProbability_one",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.originalProbability_reciprocal_bounds",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.realCount_one_color",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.Spec.reciprocal_bounds",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.from_anchored_counts",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.from_anchored_polynomials",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.lower547",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.lower548",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.originalProbability_spec",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_lower547",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_lower548",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_upper47",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_upper59",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.original_upper61",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.upper47",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.upper59",
    "OpenMathResearch.LongCycleExcedances.CycleProbability.upper61",
    "OpenMathResearch.LongCycleExcedances.binomialDensity_unimodal",
    "OpenMathResearch.LongCycleExcedances.binomialPrimitive_mass",
    "OpenMathResearch.LongCycleExcedances.binomial_grid_mass",
    "OpenMathResearch.LongCycleExcedances.binomial_grid_mass_complement",
    "OpenMathResearch.LongCycleExcedances.binomial_peak_from_scaled_bound",
    "OpenMathResearch.LongCycleExcedances.binomial_peak_from_uniform_atom",
    "OpenMathResearch.LongCycleExcedances.color_load_grid_mass",
    "OpenMathResearch.LongCycleExcedances.finite_unimodal_mesh",
    "OpenMathResearch.LongCycleExcedances.front_grid_scale",
    "OpenMathResearch.LongCycleExcedances.hasDerivAt_binomialPrimitive",
    "OpenMathResearch.LongCycleExcedances.small_lag_grid_mass",
    "OpenMathResearch.LongCycleExcedances.uniform_front_lag_budget",
    "RepositoryQuotientAudit.original_color_load_grid_mass",
    "RepositoryQuotientAudit.original_front_acceptance_upper",
    "RepositoryQuotientAudit.original_front_alpha_lower",
    "RepositoryQuotientAudit.original_front_alpha_one",
    "RepositoryQuotientAudit.original_front_alpha_upper",
    "RepositoryQuotientAudit.original_uniform_front_lag",

    "OpenMathResearch.LongCycleExcedances.color_lag_grid_upper",
    "OpenMathResearch.LongCycleExcedances.sparse_lag_large_budget",
    "OpenMathResearch.LongCycleExcedances.sparse_lag_small_budget",
    "RepositoryQuotientAudit.original_lag_le_color_grid",

    "OpenMathResearch.LongCycleExcedances.ColorAnchor.actual_color_probability_comparison",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.actual_load_lower_budget",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.actual_load_upper_budget",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.color_load_cutoff_comparison",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.color_long_load_budget",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.color_short_load_budget",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.exceptional_color_pairs_le_marks",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.expected_color_marks_product",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.marked_color_load_card",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.marked_load_probability",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.total_marked_probability",
    "OpenMathResearch.LongCycleExcedances.color_load_large_orbit_budget",
    "OpenMathResearch.LongCycleExcedances.color_load_lower_tail",
    "OpenMathResearch.LongCycleExcedances.color_load_small_orbit_budget",
    "OpenMathResearch.LongCycleExcedances.color_load_transform_budget",
    "OpenMathResearch.LongCycleExcedances.color_load_upper_tail",

    "OpenMathResearch.LongCycleExcedances.color_lag_coefficients_nonneg",
    "OpenMathResearch.LongCycleExcedances.color_lag_comparison",
    "OpenMathResearch.LongCycleExcedances.color_transform_successor",
    "OpenMathResearch.LongCycleExcedances.coeff_color_euler_operator",
    "OpenMathResearch.LongCycleExcedances.color_successor_coefficient",
    "OpenMathResearch.LongCycleExcedances.color_geom_derivative",
    "OpenMathResearch.LongCycleExcedances.color_transform_insertion",
    "RepositoryQuotientAudit.original_color_successor_exact",
    "RepositoryQuotientAudit.original_color_successor_lag",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.mem_acceptedFinset",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.perm_at_support",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.card_transitive_perms",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.accepted_at_supports",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.card_accepted_at_supports",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.card_color_supports",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.card_label_supports",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.acceptedSupportDecomposition",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.card_goodPairs_support_sum",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.goodPairsRelabel",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.taggedCount_succ",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.taggedCount_eq_finset",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.taggedCount_zero_left",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.taggedCount_zero_right",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.normalizedCount_zero_left",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.normalizedCount_succ",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.realCount_zero",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.realCount_recurrence",
    "OpenMathResearch.LongCycleExcedances.ColorAnchor.realCount_bounds",
    "RepositoryQuotientAudit.original_color_count_eq_transform",
    "RepositoryQuotientAudit.original_color_acceptance_error",
    "OpenMathResearch.LongCycleExcedances.colorPowerSeries_succ",
    "OpenMathResearch.LongCycleExcedances.color_eulerian_kernel",
    "OpenMathResearch.LongCycleExcedances.color_convolution_coeff",
    "OpenMathResearch.LongCycleExcedances.colorTransform_zero",
    "OpenMathResearch.LongCycleExcedances.colorTransform_mul",
    "OpenMathResearch.LongCycleExcedances.colorTransform_cycle",
    "OpenMathResearch.LongCycleExcedances.colorTransform_anchor",
    "OpenMathResearch.LongCycleExcedances.colorTransform_coeff",
    "OpenMathResearch.LongCycleExcedances.color_transform_error_twice",
    "OpenMathResearch.LongCycleExcedances.bar_choices_le_words",
    "OpenMathResearch.LongCycleExcedances.color_extra_bars",
    "OpenMathResearch.LongCycleExcedances.color_transform_error",
    "RepositoryQuotientAudit.original_color_count_of_recurrence",
    "RepositoryQuotientAudit.original_color_transform_anchor",
    "RepositoryQuotientAudit.original_color_series_unique",
    "RepositoryQuotientAudit.original_color_transform_error",
    "RepositoryQuotientAudit.original_interlacing_of_exterior_box_bounds",
    "RepositoryQuotientAudit.original_interlacing_of_exterior_coefficient_bounds",
    "RepositoryQuotientAudit.original_front_of_polynomial_bounds",
    "OpenMathResearch.LongCycleExcedances.polynomial_front_ordered",
    "OpenMathResearch.LongCycleExcedances.polynomial_front_singleton",
    "OpenMathResearch.LongCycleExcedances.signed_root_of_front_coefficients",
    "OpenMathResearch.LongCycleExcedances.front_coefficient_bound",
    "OpenMathResearch.LongCycleExcedances.adjacent_front_centers",
    "OpenMathResearch.LongCycleExcedances.arctan_uniform_join",
    "OpenMathResearch.LongCycleExcedances.effective_front_adjacent_centers",
    "OpenMathResearch.LongCycleExcedances.exterior_floor_budget",
    "OpenMathResearch.LongCycleExcedances.exterior_modulus_lt_phase_boundary",
    "OpenMathResearch.LongCycleExcedances.front_boxes_ordered",
    "OpenMathResearch.LongCycleExcedances.front_log_midpoint",
    "OpenMathResearch.LongCycleExcedances.front_normalize_insertion",
    "OpenMathResearch.LongCycleExcedances.front_separation_log",
    "OpenMathResearch.LongCycleExcedances.front_singleton_witness",
    "OpenMathResearch.LongCycleExcedances.front_successor_sign",
    "OpenMathResearch.LongCycleExcedances.join_signed_root_moduli",
    "OpenMathResearch.LongCycleExcedances.ordered_middle_level_roots",
    "OpenMathResearch.LongCycleExcedances.uniform_join_cutoff_separation",
    "OpenMathResearch.LongCycleExcedances.uniform_join_geometry",
    "OpenMathResearch.LongCycleExcedances.uniform_join_phase_from_imag",
    "OpenMathResearch.LongCycleExcedances.uniform_join_radius_sq",
    "RepositoryQuotientAudit.original_interlacing_of_exterior_roots",
    "RepositoryQuotientAudit.original_interlacing_of_literal_half_roots",
    "RepositoryQuotientAudit.original_ordered_middle_roots",
    "RepositoryQuotientAudit.original_principal_phase_at_zero",
    "RepositoryQuotientAudit.original_uniform_join_middle",
    "RepositoryQuotientAudit.original_uniform_join_phase",
    "RepositoryQuotientAudit.poleAngle_uniform_join",

    "OpenMathResearch.LongCycleExcedances.centered_pole_readout",
    "OpenMathResearch.LongCycleExcedances.fixed_nested_radius_budget",
    "OpenMathResearch.LongCycleExcedances.logarithmic_principal_unit",
    "OpenMathResearch.LongCycleExcedances.neighbor_pole_displacement",
    "OpenMathResearch.LongCycleExcedances.nested_decay_at_size",
    "OpenMathResearch.LongCycleExcedances.nested_far_pole_error",
    "OpenMathResearch.LongCycleExcedances.nested_near_pole_error",
    "OpenMathResearch.LongCycleExcedances.nested_pole_lattice_error",
    "OpenMathResearch.LongCycleExcedances.nested_pole_radii_error",
    "OpenMathResearch.LongCycleExcedances.nested_pole_radii_error_uniform",
    "OpenMathResearch.LongCycleExcedances.nested_size_envelope",
    "OpenMathResearch.LongCycleExcedances.normalized_nested_budget",
    "OpenMathResearch.LongCycleExcedances.signed_true_phase_cell",
    "OpenMathResearch.LongCycleExcedances.signed_true_phase_cell_anti",
    "RepositoryQuotientAudit.mem_positiveEnclosedPoles",
    "RepositoryQuotientAudit.nested_approximation_positive_half",
    "RepositoryQuotientAudit.nested_enclosed_minor_mode_mass",
    "RepositoryQuotientAudit.original_middle_centered_rows",
    "RepositoryQuotientAudit.original_middle_nested_row_error",
    "RepositoryQuotientAudit.original_middle_nested_row_error_positive_half",
    "RepositoryQuotientAudit.original_middle_phase_readout",
    "RepositoryQuotientAudit.original_middle_true_phase_cell",
    "RepositoryQuotientAudit.original_nested_row_error",
    "OpenMathResearch.LongCycleExcedances.small_log_radius_excludes",
    "RepositoryQuotientAudit.enclosed_poles_empty_of_small",
    "RepositoryQuotientAudit.all_angle_enclosed_minor_poles_le_fifth",
    "RepositoryQuotientAudit.middle_coherent_square_sum",
    "OpenMathResearch.LongCycleExcedances.all_cutoff_vertical_density_budget",
    "OpenMathResearch.LongCycleExcedances.coherent_log_chord_bound",
    "OpenMathResearch.LongCycleExcedances.coherent_vertical_transport",
    "OpenMathResearch.LongCycleExcedances.complex_exp_negative_odd_pole",
    "OpenMathResearch.LongCycleExcedances.complex_hasSum_discrete_moment",
    "OpenMathResearch.LongCycleExcedances.conjugate_logPolyAt",
    "OpenMathResearch.LongCycleExcedances.cutoffExp_deriv",
    "OpenMathResearch.LongCycleExcedances.enclosed_radius_decay",
    "OpenMathResearch.LongCycleExcedances.gamma_mesh_peak",
    "OpenMathResearch.LongCycleExcedances.log_difference_from_modes",
    "OpenMathResearch.LongCycleExcedances.long_cycle_vertical_density_budget",
    "OpenMathResearch.LongCycleExcedances.poisson_peak_le_ninth",
    "OpenMathResearch.LongCycleExcedances.shifted_complex_geometric",
    "OpenMathResearch.LongCycleExcedances.unimodal_density_mesh",
    "OpenMathResearch.LongCycleExcedances.vertical_mode_transport",
    "OpenMathResearch.LongCycleExcedances.vertical_radius_power",
    "OpenMathResearch.LongCycleExcedances.weighted_minor_poles_le_fifth",
    "OpenMathResearch.LongCycleExcedances.weighted_odd_mode_bound",
    "RepositoryQuotientAudit.actualLogTiltAt_principal",
    "RepositoryQuotientAudit.actual_enclosed_minor_poles_le_fifth",
    "RepositoryQuotientAudit.actual_logTilt_far_exp_ratio",
    "RepositoryQuotientAudit.actual_logTilt_far_pole",
    "RepositoryQuotientAudit.actual_logTilt_pole_chord",
    "RepositoryQuotientAudit.coherentPole_exp_neg",
    "RepositoryQuotientAudit.cutoffLogCoefficient_hasSum",
    "RepositoryQuotientAudit.enclosed_coherent_radial_decay",
    "RepositoryQuotientAudit.principalLogTilt_im_bound",
    "OpenMathResearch.LongCycleExcedances.discrete_low_frequency_sum",
    "OpenMathResearch.LongCycleExcedances.discrete_low_mode",
    "OpenMathResearch.LongCycleExcedances.expPrefix_half_bound",
    "OpenMathResearch.LongCycleExcedances.large_linear_cost",
    "OpenMathResearch.LongCycleExcedances.lowCut_scale",
    "OpenMathResearch.LongCycleExcedances.low_moment_absolute_mass",
    "OpenMathResearch.LongCycleExcedances.pole_monomial_bound",
    "OpenMathResearch.LongCycleExcedances.shifted_moment_input",
    "OpenMathResearch.LongCycleExcedances.small_linear_cost",
    "OpenMathResearch.LongCycleExcedances.square_majorized_lattice",
    "OpenMathResearch.LongCycleExcedances.uniform_contour_factor",
    "OpenMathResearch.LongCycleExcedances.uniform_high_degree_contour_factor",
    "OpenMathResearch.LongCycleExcedances.uniform_high_degree_lattice",
    "OpenMathResearch.LongCycleExcedances.uniform_high_degree_odd_poles",
    "OpenMathResearch.LongCycleExcedances.uniform_high_degree_scale_of_cut",
    "OpenMathResearch.LongCycleExcedances.uniform_mass_from_split",
    "OpenMathResearch.LongCycleExcedances.uniform_outer_radius",
    "OpenMathResearch.LongCycleExcedances.uniform_small_modulus_odd_poles",
    "RepositoryQuotientAudit.original_uniform_log_mass",
    "RepositoryQuotientAudit.original_uniform_tilt_envelope",
    "RepositoryQuotientAudit.uniform_high_degree_coherent_multiplier",
    "RepositoryQuotientAudit.uniform_high_degree_coherent_poles",
    "RepositoryQuotientAudit.uniform_small_modulus_coherent_multiplier",
    "RepositoryQuotientAudit.uniform_small_modulus_coherent_poles",
    "RepositoryQuotientAudit.original_ordered_high_angle_roots",
    "OpenMathResearch.LongCycleExcedances.ordered_grid_roots",
    "OpenMathResearch.LongCycleExcedances.phase_slope_bound",
    "OpenMathResearch.LongCycleExcedances.poleAngle_hasDerivAt",
    "OpenMathResearch.LongCycleExcedances.two_sided_far_remainder",
    "RepositoryQuotientAudit.high_angle_scaled_far_bound",
    "RepositoryQuotientAudit.all_angle_scaled_remainder",
    "RepositoryQuotientAudit.all_angle_far_lattice",
    "RepositoryQuotientAudit.principal_far_geometry",
    "RepositoryQuotientAudit.middle_slope_from_moment",
    "RepositoryQuotientAudit.original_high_angle_cells",
    "RepositoryQuotientAudit.signed_original_high_angle_cell_of_pole_tail",
    "RepositoryQuotientAudit.original_angular_phase_remainder",
    "RepositoryQuotientAudit.angleLogTilt_center",
    "RepositoryQuotientAudit.signed_original_high_angle_cell",
    "RepositoryQuotientAudit.original_middle_phase_strictAnti",
    "RepositoryQuotientAudit.original_middle_phase_slope",
    "OpenMathResearch.LongCycleExcedances.high_angle_displacement_of_deriv",
    "OpenMathResearch.LongCycleExcedances.high_angle_displacement",
    "OpenMathResearch.LongCycleExcedances.cosecant_oscillation_variation",
    "OpenMathResearch.LongCycleExcedances.signed_grid_cell_of_row_estimates",
    "OpenMathResearch.LongCycleExcedances.angular_pole_geometry",
    "OpenMathResearch.LongCycleExcedances.phase_readout_cis",
    "OpenMathResearch.LongCycleExcedances.angular_phase_remainder",
    "OpenMathResearch.LongCycleExcedances.logarithmCoeff_hasDerivAt",
    "OpenMathResearch.LongCycleExcedances.finiteTilt_diagonal_hasDerivAt",
    "OpenMathResearch.LongCycleExcedances.seventh_mesh_bound",
    "OpenMathResearch.LongCycleExcedances.seventh_far_summable_bound",
    "OpenMathResearch.LongCycleExcedances.middle_derivative_error",
    "OpenMathResearch.LongCycleExcedances.signed_cos_grid",
    "OpenMathResearch.LongCycleExcedances.signed_sin_grid_cell",
    "RepositoryQuotientAudit.actual_principalLogTilt_derivative",
    "RepositoryQuotientAudit.original_coherentTilt_coeff_bound",
    "RepositoryQuotientAudit.seriesValue_original_coherentTilt",
    "RepositoryQuotientAudit.norm_seriesValue_coherentTilt_ge",
    "RepositoryQuotientAudit.actual_high_angle_log_mass",
    "RepositoryQuotientAudit.actual_high_angle_row_error",
    "RepositoryQuotientAudit.actual_high_angle_normalized_error",
    "RepositoryQuotientAudit.original_high_angle_next_sign",
    "OpenMathResearch.LongCycleExcedances.high_angle_geometric_envelope",
    "OpenMathResearch.LongCycleExcedances.next_sign_of_unit_principal_mode",
    "OpenMathResearch.LongCycleExcedances.norm_far_pole_truncation_le",
    "RepositoryQuotientAudit.original_logistic_coefficient",
    "RepositoryQuotientAudit.original_rescaled_logTilt_coeff",
    "RepositoryQuotientAudit.coherent_product_coefficient",
    "RepositoryQuotientAudit.coherent_successor_coefficient",
    "RepositoryQuotientAudit.original_coherent_row_pair",
    "RepositoryQuotientAudit.original_normalized_pole_profile",
    "RepositoryQuotientAudit.original_nonprincipal_profile_bound",
    "OpenMathResearch.FirstLevelHits.exists_firstLevelHitOn",
    "OpenMathResearch.FirstLevelHits.exists_lastLower_before_firstUpper",
    "OpenMathResearch.LongCycleExcedances.singleton_windows_of_phase",
    "RepositoryQuotientAudit.generalCycleQuotient_eq_divX",
    "RepositoryQuotientAudit.original_divX_shape",
    "RepositoryQuotientAudit.exact_coeff_eq_divX",
    "RepositoryQuotientAudit.canonical_eq_external_divX",
    "RepositoryQuotientAudit.original_signed_point_of_rational_margin",
    "RepositoryQuotientAudit.strict_of_complete_moduli",
    "RepositoryQuotientAudit.original_weak_of_complete_moduli",
    "RepositoryQuotientAudit.original_weak_of_mixed_windows",
    "RepositoryQuotientAudit.original_divX_reciprocity",
    "RepositoryQuotientAudit.original_weak_of_half_axis_windows",
    "RepositoryQuotientAudit.original_even_center",
    "RepositoryQuotientAudit.original_next_center_sign",
    "RepositoryQuotientAudit.original_weak_of_left_windows",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(project, *args, capture=False):
    return subprocess.run(args, cwd=project, text=True, check=True,
                          stdout=subprocess.PIPE if capture else None).stdout


def prepare(project):
    pin = runpy.run_path(str(COEFFICIENTS / "check.py"))
    commit = pin["COMMIT"]
    source = f"https://raw.githubusercontent.com/AlexZander-666/long-cycle-excedance-interlacing/{commit}"
    with urllib.request.urlopen(source + "/cutoff-six/formal/cutoff-six-all-accepted.zip", timeout=45) as response:
        outer = response.read()
    pin["check_digest"](outer, pin["OUTER"])
    with ZipFile(io.BytesIO(outer)) as archive:
        inner = archive.read("cutoff-six-all-source.zip")
    pin["check_digest"](inner, pin["INNER"])
    with ZipFile(io.BytesIO(inner)) as archive:
        if any(Path(name).is_absolute() or ".." in Path(name).parts for name in archive.namelist()):
            raise ValueError("invalid path in frozen source archive")
        archive.extractall(project)
    run(project, "sha256sum", "--quiet", "-c", "SHA256SUMS")
    pin["check_digest"]((project / "lake-manifest.json").read_bytes(), pin["MANIFEST"])
    assert (project / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    print(f"Frozen upstream source {commit}", flush=True)


def compile_topic(project):
    files = [
        (SHARED / "OpenMathResearch/FirstLevelHits.lean", "OpenMathResearch/FirstLevelHits"),
        (SHARED / "OpenMathResearch/AlternatingSignRoots.lean", "OpenMathResearch/AlternatingSignRoots"),
        (TOPIC / "LongCyclePhaseWindows.lean", "LongCyclePhaseWindows"),
        (SHARED / "OpenMathResearch/OrientedNegativeInterlace.lean", "OpenMathResearch/OrientedNegativeInterlace"),
        (SHARED / "OpenMathResearch/DiskUniqueness.lean", "OpenMathResearch/DiskUniqueness"),
        (TOPIC / "LongCycleMixedRootWitnesses.lean", "LongCycleMixedRootWitnesses"),
        (TOPIC / "LongCyclePrefixTail.lean", "LongCyclePrefixTail"),
        (TOPIC / "LongCycleRunColors.lean", "LongCycleRunColors"),
        (TOPIC / "LongCycleReducedRow.lean", "LongCycleReducedRow"),
        (COEFFICIENTS / "RepositoryQuotientAdapter.lean", "RepositoryQuotientAdapter"),
        (HERE / "RationalPointSound.lean", "RationalPointSound"),
        (HERE / "RepositoryQuotientShape.lean", "RepositoryQuotientShape"),
        (HERE / "RepositoryActualRationalPoint.lean", "RepositoryActualRationalPoint"),
        (HERE / "StrictRootListTranslation.lean", "StrictRootListTranslation"),
        (HERE / "RepositoryRootAssembly.lean", "RepositoryRootAssembly"),
        (HERE / "ReciprocalWindowSigns.lean", "ReciprocalWindowSigns"),
        (HERE / "ReciprocalHalfWindows.lean", "ReciprocalHalfWindows"),
        (HERE / "RepositoryHalfAxisAssembly.lean", "RepositoryHalfAxisAssembly"),
        (HERE / "ReciprocalCenterSign.lean", "ReciprocalCenterSign"),
        (HERE / "RepositoryCenterSign.lean", "RepositoryCenterSign"),
    ]
    files.append((HERE / "RepositoryPoleProfile.lean", "RepositoryPoleProfile"))
    files.append((HERE / "RepositoryCoherentPoles.lean", "RepositoryCoherentPoles"))
    files.append((HERE / "FarPoleTruncation.lean", "FarPoleTruncation"))
    files.append((HERE / "MonomialTiltBounds.lean", "MonomialTiltBounds"))
    files.append((HERE / "TiltAnalyticEvaluation.lean", "TiltAnalyticEvaluation"))
    files.append((HERE / "HighAngleScalar.lean", "HighAngleScalar"))
    files.append((HERE / "HighAngleLattice.lean", "HighAngleLattice"))
    files.append((HERE / "HighAngleActualInputs.lean", "HighAngleActualInputs"))
    files.append((HERE / "HighAngleRowEstimate.lean", "HighAngleRowEstimate"))
    files.append((HERE / "ActualHighAngleSign.lean", "ActualHighAngleSign"))
    files.extend((TOPIC.parent / "phase-cells" / (name + ".lean"), name) for name in PHASE_MODULES)
    files.extend((TOPIC / "uniform-log-tilt" / (m + ".lean"), m) for m in UNIFORM_MODULES)
    files.extend((TOPIC / "vertical-tilt" / (m + ".lean"), m) for m in VERTICAL_MODULES)
    files.extend((TOPIC / "middle-residues" / (m + ".lean"), m) for m in MIDDLE_MODULES)
    files.extend((TOPIC / "front-middle-join" / (m + ".lean"), m) for m in JOIN_MODULES)
    files.extend((TOPIC.parent / "color-acceptance" / (m + ".lean"), m) for m in COLOR_MODULES)
    files.extend((TOPIC / "probability-bands" / (m + ".lean"), m) for m in BAND_MODULES)
    files.extend((TOPIC.parent / "color-load-bounds" / (m + ".lean"), m) for m in LOAD_MODULES)
    observed = {}
    failed = set()
    for source, module in files:
        target = project / (module + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        patch = SHARED / "publication/ports" / (module.replace("/", ".") + ".patch")
        if module in {"OpenMathResearch/AlternatingSignRoots", "OpenMathResearch/OrientedNegativeInterlace"}:
            with patch.open() as edits:
                subprocess.run(["patch", "--batch", str(target)], stdin=edits, text=True, check=True)
        if module == "LongCycleRunColors":
            target.write_text(target.read_text().replace("Polynomial.finset_sum_coeff", "Polynomial.finsetSum_coeff"))
        if module == "LongCyclePrefixTail":
            # add_le_add_left changed orientation in the pinned Mathlib.
            target.write_text(target.read_text().replace(
                "add_le_add_left hlo _, add_le_add_left hhi _",
                "add_le_add (le_refl (c 0)) hlo, add_le_add (le_refl (c 0)) hhi",
            ))
        module_name = module.replace("/", ".")
        imports = re.findall(r"^import ([\w.]+)", target.read_text(), flags=re.M)
        if failed.intersection(imports):
            failed.add(module_name)
            print(f"Skip {module_name} after an import failed", flush=True)
            continue
        out = project / ".lake/build/lib/lean" / (module + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        print(f"Compile {module} input-sha256={sha256(target.read_bytes()).hexdigest()}", flush=True)
        command = ["lake", "env", "lean", "-o", str(out), str(target)]
        result = subprocess.run(command, cwd=project, text=True, stdout=subprocess.PIPE)
        print(result.stdout, end="", flush=True)
        if result.returncode:
            failed.add(module_name)
            continue
        records = re.findall(
            r"^'((?:RepositoryQuotientAudit|OpenMathResearch)\.[^']+)' "
            r"(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
            result.stdout, flags=re.M,
        )
        for name, axioms in records:
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
    if failed:
        raise ArithmeticError(f"Modules not compiled: {sorted(failed)}")
    for name in EXPECTED:
        if name not in observed or observed[name] - ALLOWED:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {name}: {observed.get(name)}")
    for module in ("RationalPointSound", "RepositoryQuotientShape", "RepositoryActualRationalPoint",
                   "StrictRootListTranslation", "RepositoryRootAssembly", "ReciprocalWindowSigns",
                   "ReciprocalHalfWindows", "RepositoryHalfAxisAssembly",
                   "ReciprocalCenterSign", "RepositoryCenterSign",
                   "OpenMathResearch.FirstLevelHits", "LongCyclePhaseWindows", "RepositoryPoleProfile", "RepositoryCoherentPoles",
                   "FarPoleTruncation", "MonomialTiltBounds", "TiltAnalyticEvaluation",
                   "HighAngleScalar", "HighAngleLattice", "HighAngleActualInputs", "HighAngleRowEstimate", "ActualHighAngleSign", *PHASE_MODULES, *UNIFORM_MODULES, *VERTICAL_MODULES, *MIDDLE_MODULES, *JOIN_MODULES, *COLOR_MODULES, *BAND_MODULES, *LOAD_MODULES):
        run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(EXPECTED)} declarations audited", flush=True)


def main(project, imports):
    project.mkdir(parents=True)
    prepare(project)
    version = run(project, "lean", "--version", capture=True).strip()
    if COMPILER not in version:
        raise ValueError(f"unexpected compiler {version}")
    print(version, flush=True)
    run(project, "lake", "exe", "cache", "get")
    mathlib = run(project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD", capture=True).strip()
    if mathlib != MATHLIB:
        raise ValueError(f"unexpected mathlib {mathlib}")
    print(f"mathlib {mathlib}", flush=True)
    if imports is None:
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient")
    else:
        digest = sha256(imports.read_bytes()).hexdigest()
        if digest != IMPORT_SHA:
            raise ValueError(f"unexpected retained object archive {digest}")
        run(project, "tar", "--zstd", "-xf", str(imports))
        print(f"Reused verified 65-module archive sha256={digest}", flush=True)
    for module in (*LOGISTIC_IMPORTS, "UniversalRecurrence"):
        name = "LongCycleBounds/" + module
        source = project / (name + ".lean")
        out = project / ".lake/build/lib/lean" / (name + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        print(f"Compile {name} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
        run(project, "lake", "env", "lean", "-o", str(out), str(source))
    compile_topic(project)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
