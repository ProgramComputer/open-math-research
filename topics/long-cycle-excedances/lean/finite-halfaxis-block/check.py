#!/usr/bin/env python3
"""Build the largest-size directed arithmetic pilot on the cutoff-eight pin."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import resource
import runpy
import shutil
import signal
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FIRST = runpy.run_path(str(HERE.parent / "finite-halfaxis" / "check.py"))
ARCHIVE = HERE.parents[3] / FIRST["ARCHIVE"]
MEMORY = 6 * 1024**3
TIMEOUT = 180
SUPPORT = {
    "ShortInsertion": {"shortExactStep_eq", "compactCycleWeight_support"},
    "SplitHalfAxis": {"halfAxisDyadicOK_of_split"},
    "ArithmeticBlocks": {"arithmeticBlock_read"},
    "LargePilotAudit": {"insertion_249", "insertion_250", "windows_249", "windows_250"},
}


def limit_address_space():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


def guarded(project, module, phase, *command):
    proc = subprocess.Popen(
        ["/usr/bin/time", "-v", *command], cwd=project, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        start_new_session=True, preexec_fn=limit_address_space,
    )
    try:
        log, _ = proc.communicate(timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        log, _ = proc.communicate()
        print(log, end="", flush=True)
        raise TimeoutError(f"{module} {phase} exceeded {TIMEOUT} seconds") from None
    print(log, end="", flush=True)
    if proc.returncode:
        raise RuntimeError(f"{module} {phase} exited {proc.returncode} at AS cap {MEMORY} bytes")
    print(f"phase_exit=0 {module} {phase}", flush=True)
    return log


def build(project, name, source, audit, replay):
    target = project / (name + ".lean")
    shutil.copyfile(source, target)
    digest = sha256(target.read_bytes()).hexdigest()
    print(f"Compile {name} sha256={digest} AS_cap={MEMORY} timeout={TIMEOUT}", flush=True)
    out = project / ".lake/build/lib/lean" / (name + ".olean")
    log = guarded(project, name, "compile", "lake", "env", "lean", "-j=1",
                  "-DwarningAsError=true", "-o", str(out), str(target))
    observed = {}
    for full_name, values in re.findall(
        r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
        log, re.M,
    ):
        observed[full_name.rsplit(".",1)[-1]] = {a.strip() for a in values.split(",") if a.strip()}
    if set(observed) != audit:
        raise ValueError(f"{name} axiom declarations {set(observed)} do not match {audit}")
    if any(values - FIRST["COMMON"]["ALLOWED"] for values in observed.values()):
        raise ValueError(f"{name} used an unexpected axiom")
    if replay:
        guarded(project, name, "kernel", "lake", "env", "leanchecker", "--verbose", name)


def check(project, retained):
    FIRST["check"](project, retained)
    for module in ("ShortInsertion", "SplitHalfAxis", "ArithmeticBlocks"):
        build(project, module, HERE / (module + ".lean"), SUPPORT[module], True)
    folder = project / "generated-cutoff-eight"
    manifest = json.loads(subprocess.check_output(
        [sys.executable, "-B", str(HERE / "generate.py"), str(folder), str(ARCHIVE), "--pilot"],
        text=True,
    ))
    names = [*manifest["data"], "FiniteCutoffEightData",
             *manifest["step"], *manifest["signs"],
             *manifest["stepJoin"], *manifest["pointJoin"]]
    if len(names) != 18:
        raise ValueError(f"Unexpected pilot module count {len(names)}")
    for module in names:
        build(project, module, folder / (module + ".lean"), set(),
              module in manifest["step"] or module in manifest["signs"])
    build(project, "LargePilotAudit", HERE / "LargePilotAudit.lean", SUPPORT["LargePilotAudit"], True)
    print("PASS: exact high-rank pilot for old sizes 249 and 250", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("retained", type=Path, nargs="?")
    args = parser.parse_args()
    check(args.project.resolve(), args.retained.resolve(strict=True) if args.retained else None)
