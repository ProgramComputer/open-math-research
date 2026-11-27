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
    print(f"PASS: {len(EXPECTED)} exterior declarations audited", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
