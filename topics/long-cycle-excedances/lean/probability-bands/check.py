"""Compile and audit cycle probability bounds against the frozen literal enumerator."""

import argparse
import re
import runpy
import shutil
import subprocess
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMMON = runpy.run_path(str(HERE.parent / "common-pin/check.py"))
MODULES = ("CycleProbabilityBands", "AnchoredProbability", "RepositoryProbabilityBands")
PREFIX = "OpenMathResearch.LongCycleExcedances.CycleProbability."
REQUIRED = {
    PREFIX + name
    for name in (
        "from_anchored_counts",
        "from_anchored_polynomials",
        "originalProbability_spec",
        "original_upper61",
        "original_upper59",
        "original_upper47",
        "original_lower547",
        "original_lower548",
    )
}


def verify(project, imports):
    run = COMMON["run"]
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    version = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in version:
        raise ValueError(f"Unexpected compiler {version}")
    print(version, flush=True)
    run(project, "lake", "exe", "cache", "get")
    mathlib = run(project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD",
                  capture=True).strip()
    if mathlib != COMMON["MATHLIB"]:
        raise ValueError(f"Unexpected mathlib {mathlib}")
    print(f"mathlib {mathlib}", flush=True)
    if imports is None:
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient")
    else:
        digest = sha256(imports.read_bytes()).hexdigest()
        if digest != COMMON["IMPORT_SHA"]:
            raise ValueError(f"Unexpected retained object archive {digest}")
        run(project, "tar", "--zstd", "-xf", str(imports))
        print(f"Reused audited upstream object archive sha256={digest}", flush=True)

    observed = {}
    failed = set()
    for module in MODULES:
        target = project / (module + ".lean")
        shutil.copy2(HERE / target.name, target)
        dependencies = set(re.findall(r"^import ([\w.]+)", target.read_text(), flags=re.M))
        if failed & dependencies:
            failed.add(module)
            continue
        output = project / ".lake/build/lib/lean" / (module + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"Compile {module} input-sha256={sha256(target.read_bytes()).hexdigest()}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", "-o", str(output), str(target)],
            cwd=project,
            text=True,
            stdout=subprocess.PIPE,
        )
        print(result.stdout, end="", flush=True)
        if result.returncode:
            failed.add(module)
            continue
        records = re.findall(
            r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
            result.stdout,
            flags=re.M,
        )
        for name, axioms in records:
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
    if failed:
        raise ArithmeticError(f"Modules not compiled: {sorted(failed)}")
    for name in REQUIRED:
        if name not in observed or observed[name] - COMMON["ALLOWED"]:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {name}")
    for module in MODULES:
        run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(REQUIRED)} normalization and original probability declarations audited",
          flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new working directory")
    parser.add_argument("imports", type=Path, nargs="?")
    args = parser.parse_args()
    verify(args.project.resolve(), args.imports.resolve() if args.imports else None)
