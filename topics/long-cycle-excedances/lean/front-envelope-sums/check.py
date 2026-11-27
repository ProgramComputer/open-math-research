#!/usr/bin/env python3
"""Check the exterior coefficient-sum proof using the shared research pin."""

import importlib.util
import re
import shutil
import subprocess
import sys
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
MODULES = (
    "FrontNormAlgebra",
    "FrontFiniteSums",
    "FrontEnvelopeSum",
    "FrontLagSum",
    "FrontSmallCap",
    "RepositoryExteriorEnvelopes",
)
SECTOR_MODULES = (
    "AdaptiveFrontBounds",
    "AdaptiveFrontWeights",
    "AdaptiveFrontGap",
    "RepositoryOldFrontTails",
    "ExteriorScaleOrder",
    "RepositorySparseSector",
    "SparseSizeThreshold",
)
ASPECT_MODULES = (
    "ResidualLagGrid",
    "SharpLagBudget",
    "OriginalResidualLag",
    "TwoGridLag",
    "ZeroResidualLag",
    "RepositorySharpNearLag",
    "ExteriorIntegerSeam",
    "RepositoryAllAspectExterior",
    "AllAspectExterior",
)
EXPECTED = {
    "OpenMathResearch.LongCycleExcedances." + name
    for name in (
        "front_norm_closed_successor",
        "front_next_residual_eq",
        "front_finite_geometric_bound",
        "front_norm_of_two_geometric_tails",
        "front_old_and_centered_norm",
        "front_norm_old_full",
        "front_norm_lag",
        "front_certificates_of_weighted_envelopes",
        "front_lag_cutoff_gap",
        "front_cap_lt_half",
    )
} | {"RepositoryQuotientAudit.original_interlacing_of_exterior_weighted_envelopes"}
ASPECT_EXPECTED = {
    "OpenMathResearch.LongCycleExcedances.binomial_residual_identity",
    "OpenMathResearch.LongCycleExcedances.color_lag_residual_grid",
    "OpenMathResearch.LongCycleExcedances.color_load_grid_mass_sharp",
    "OpenMathResearch.LongCycleExcedances.exterior_cap_before_integer_seam",
    "OpenMathResearch.LongCycleExcedances.exterior_integer_seam_geometry",
    "OpenMathResearch.LongCycleExcedances.exterior_integer_seam_log_pos",
    "OpenMathResearch.LongCycleExcedances.front_lag_zero_of_residual_count",
    "OpenMathResearch.LongCycleExcedances.modal_bound_two_grids",
    "OpenMathResearch.LongCycleExcedances.real_count_below_cutoff",
    "OpenMathResearch.LongCycleExcedances.sharp_front_lag_of_two_color_grids",
    "OpenMathResearch.LongCycleExcedances.two_color_load_grids_mass",
    "OpenMathResearch.LongCycleExcedances.two_grid_relative_lag",
    "RepositoryQuotientAudit.original_all_aspect_exterior",
    "RepositoryQuotientAudit.original_exterior_coefficient_tests_all",
    "RepositoryQuotientAudit.original_exterior_root_witnesses_all",
    "RepositoryQuotientAudit.original_exterior_roots_before_integer_seam",
    "RepositoryQuotientAudit.original_far_front_weighted_lag_all",
    "RepositoryQuotientAudit.original_front_adjacent_gap_all",
    "RepositoryQuotientAudit.original_front_alpha_ratio_all",
    "RepositoryQuotientAudit.original_front_lag_relative_of_alpha",
    "RepositoryQuotientAudit.original_front_lag_zero_at_high_cutoff",
    "RepositoryQuotientAudit.original_front_scale_cap_all",
    "RepositoryQuotientAudit.original_lag_residual_grid",
    "RepositoryQuotientAudit.original_near_lag_all_aspects",
    "RepositoryQuotientAudit.original_old_front_weighted_tails_all",
    "RepositoryQuotientAudit.original_residual_count_bound",
}
SECTOR_EXPECTED = {
    "OpenMathResearch.LongCycleExcedances.sparse_size_log_threshold",
    "OpenMathResearch.LongCycleExcedances.sparse_sector_from_cutoff_threshold",
    "RepositoryQuotientAudit.original_sparse_interlacing_from_cutoff",
    "RepositoryQuotientAudit.original_front_scale_cap",
    "OpenMathResearch.LongCycleExcedances.adaptive_front_adjacent_gap",
    "OpenMathResearch.LongCycleExcedances.exterior_alpha_ratio",
    "OpenMathResearch.LongCycleExcedances.exterior_scales_ordered",
    "OpenMathResearch.LongCycleExcedances.front_adaptive_multipliers",
    "OpenMathResearch.LongCycleExcedances.front_bare_left_weight",
    "OpenMathResearch.LongCycleExcedances.front_bare_right_weight",
    "OpenMathResearch.LongCycleExcedances.front_far_rank_geometry",
    "OpenMathResearch.LongCycleExcedances.front_far_reciprocal",
    "OpenMathResearch.LongCycleExcedances.front_far_weighted_lag",
    "OpenMathResearch.LongCycleExcedances.front_inverse_growth_bound",
    "OpenMathResearch.LongCycleExcedances.front_inverse_growth_small_rank",
    "OpenMathResearch.LongCycleExcedances.front_left_bare_ratio",
    "OpenMathResearch.LongCycleExcedances.front_right_bare_ratio",
    "RepositoryQuotientAudit.original_adaptive_front_scale",
    "RepositoryQuotientAudit.original_far_front_weighted_lag",
    "RepositoryQuotientAudit.original_front_adjacent_gap",
    "RepositoryQuotientAudit.original_front_alpha_ratio",
    "RepositoryQuotientAudit.original_old_front_weighted_tails",
    "RepositoryQuotientAudit.original_sparse_sector_interlacing",
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
    common.main(project, imports)

    observed = {}
    failed = set()
    for module in (*MODULES, *SECTOR_MODULES, *ASPECT_MODULES):
        directory = HERE if module in MODULES else HERE.parent / "sparse-sector"
        if module in ASPECT_MODULES:
            directory = HERE.parent / "all-aspect-exterior"
        source = project / (module + ".lean")
        shutil.copyfile(directory / source.name, source)
        dependencies = re.findall(r"^import ([\w.]+)", source.read_text(), flags=re.M)
        if failed.intersection(dependencies):
            failed.add(module)
            print(f"Skip {module} after an import failed", flush=True)
            continue
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
            failed.add(module)
            continue
        for name, axioms in AXIOM_REPORT.findall(result.stdout):
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}

    if failed:
        raise ArithmeticError(f"Modules not compiled: {sorted(failed)}")
    for name in sorted(EXPECTED | SECTOR_EXPECTED | ASPECT_EXPECTED):
        if name not in observed or observed[name] - common.ALLOWED:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {name}: {observed.get(name)}")
    for module in (*MODULES, *SECTOR_MODULES, *ASPECT_MODULES):
        common.run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(EXPECTED | SECTOR_EXPECTED | ASPECT_EXPECTED)} exterior and sector declarations audited", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
