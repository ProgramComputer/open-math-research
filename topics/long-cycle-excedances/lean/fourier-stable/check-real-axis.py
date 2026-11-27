#!/usr/bin/env python3
"""Check the real-axis bridge against the authenticated cutoff-six source."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import shutil


HERE = Path(__file__).resolve().parent
COMMON = runpy.run_path(str(HERE.parent / "common-pin" / "check.py"))
UPSTREAM = "LongCycleBounds.PartialFractions"
NAMESPACE = "OpenMathResearch.LongCycleExcedances."
REAL_AXIS = ("FourierRealAxis", ("fourier_squared_poles_real_axis",))
ORIGINAL_LOG = ("FourierOriginalLog", ("original_cutoff_log_linear", "original_cutoff_log_poles"))
ORIGINAL_ROOTS = ("LongCycleBounds.BandMoments", "LongCycleBounds.CycleProfileLogistic")
ORIGINAL_SUPPORT = ("RepositoryCoherentPoles", "MonomialTiltBounds")


def build_local(project, original, module, theorems):
    run = COMMON["run"]
    source = project / (module + ".lean")
    shutil.copyfile(original, source)
    output = project / ".lake" / "build" / "lib" / "lean" / (module + ".olean")
    print(f"Compile {module} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    strict = ("-DwarningAsError=true",) if theorems else ()
    audit = run(project, "lake", "env", "lean", *strict, "-o", str(output), str(source), capture=True)
    print(audit, end="", flush=True)
    for theorem in theorems:
        name = re.escape(NAMESPACE + theorem)
        match = re.findall(rf"^'{name}' depends on axioms:\s*\[([^\]]*)\]$", audit, re.M)
        if len(match) != 1 or {axiom.strip() for axiom in match[0].split(",")} - COMMON["ALLOWED"]:
            raise ValueError(f"Missing declaration or unexpected transitive axiom for {theorem}")
    if theorems:
        run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)


def main(project, original_log):
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    upstream = (UPSTREAM, *ORIGINAL_ROOTS) if original_log else (UPSTREAM,)
    suppliers = [Path(*module.split(".")).with_suffix(".lean") for module in upstream]
    run(project, "lake", "exe", "cache", "get", *map(str, suppliers))
    lock = json.loads((project / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        checkout = ".lake/packages/" + package["name"]
        revision = run(project, "git", "-C", checkout, "rev-parse", "HEAD", capture=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Wrong revision for {package['name']}: {revision}")
        print(f"{package['name']} {revision}", flush=True)
    for module, supplier in zip(upstream, suppliers, strict=True):
        digest = sha256((project / supplier).read_bytes()).hexdigest()
        print(f"Compile {module} input-sha256={digest}", flush=True)
    run(project, "lake", "--wfail", "build", *("+" + module for module in upstream))
    build_local(project, HERE / "FourierRealAxis.lean", *REAL_AXIS)
    if original_log:
        for module in ORIGINAL_SUPPORT:
            original = HERE.parent / "common-pin" / (module + ".lean")
            build_local(project, original, module, ())
        build_local(project, HERE / "FourierOriginalLog.lean", *ORIGINAL_LOG)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a new directory for the check")
    parser.add_argument("--original-log", action="store_true", help="also check the original cutoff logarithm")
    args = parser.parse_args()
    main(args.project.resolve(), args.original_log)
