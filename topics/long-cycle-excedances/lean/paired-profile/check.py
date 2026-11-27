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
MODULES = ('FinitePoleProduct', 'PairedPoleFamily', 'PairedPoleConvergence', 'PairedCycleNormalization', 'PairedCoefficientLimit', 'ScaledCycleProfile', 'RepositoryPairedCycleLift', 'RepositoryScaledCycleProfile')
EXPECTED = {
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

    observed = {}
    for module in MODULES:
        source = project / (module + ".lean")
        shutil.copyfile(HERE / source.name, source)
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
    for module in MODULES:
        common.run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(EXPECTED)} paired-profile declarations audited", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
