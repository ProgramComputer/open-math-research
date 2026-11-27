#!/usr/bin/env python3
"""Check the real-axis bridge against the authenticated cutoff-six source."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
COMMON = runpy.run_path(str(HERE.parent / "common-pin" / "check.py"))
UPSTREAM = "LongCycleBounds.PartialFractions"
NAMESPACE = "OpenMathResearch.LongCycleExcedances."
REAL_AXIS = ("FourierRealAxis", ("fourier_squared_poles_real_axis",))
ORIGINAL_LOG = ("FourierOriginalLog", ("original_cutoff_log_linear", "original_cutoff_log_poles"))
ORIGINAL_ROOTS = ("LongCycleBounds.BandMoments", "LongCycleBounds.CycleProfileLogistic")
ORIGINAL_SUPPORT = ("RepositoryCoherentPoles", "MonomialTiltBounds")


CONTINUATION = (
    ("FourierRealContinuation", ("analytic_eq_off_poles_of_real_ray",)),
    ("FourierLogisticPoles", ("logistic_denominator_zero_iff", "negative_logistic_slope_analytic")),
    ("FourierLocalPoleBounds", ("local_pole_ratio",)),
    ("FourierResolventDerivative", ("anchoredPoleSum_hasDerivAt", "inverseSquarePoleSum_analytic")),
    ("FourierGeometricRemainder", ("pole_remainder_summable", "anchoredPoleSum_taylor_remainder")),
    ("FourierAnchoredLogistic", ("rowPole_summable", "rowPole_inverseSquare_of_real", "rowPole_anchored_of_real")),
    ("FourierCutoffLogSlope", ("finiteFourierLog_deriv", "finiteFourierSlope_remainder", "finiteFourierQuotient_deriv")),
    ("FourierRowAngularEquation", ("angular_cutoff_remainder", "angular_finite_fourier_row")),
    ("FourierOriginalAngularRow", ("original_row_angular_equation",)),
)

def build_local(project, original, module, theorems):
    run = COMMON["run"]
    source = project / (module + ".lean")
    shutil.copyfile(original, source)
    output = project / ".lake" / "build" / "lib" / "lean" / (module + ".olean")
    print(f"Compile {module} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    strict = ("-DwarningAsError=true",) if theorems else ()
    try:
        audit = run(project, "lake", "env", "lean", *strict, "-o", str(output), str(source), capture=True)
    except subprocess.CalledProcessError as error:
        print(error.stdout or "", end="", flush=True)
        raise
    print(audit, end="", flush=True)
    for theorem in theorems:
        name = re.escape(NAMESPACE + theorem)
        match = re.findall(rf"^'{name}' depends on axioms:\s*\[([^\]]*)\]$", audit, re.M)
        if len(match) != 1 or {axiom.strip() for axiom in match[0].split(",")} - COMMON["ALLOWED"]:
            raise ValueError(f"Missing declaration or unexpected transitive axiom for {theorem}")
    if theorems:
        run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)


def build_upstream(project, upstream, retained_imports):
    run = COMMON["run"]
    for module in upstream:
        supplier = project / Path(*module.split(".")).with_suffix(".lean")
        print(f"Upstream {module} input-sha256={sha256(supplier.read_bytes()).hexdigest()}", flush=True)
    if retained_imports is None:
        run(project, "lake", "--wfail", "build", *("+" + module for module in upstream))
        return
    digest = sha256(retained_imports.read_bytes()).hexdigest()
    if digest != COMMON["IMPORT_SHA"]:
        raise ValueError(f"Unexpected retained object archive: {digest}")
    run(project, "tar", "--zstd", "-xf", str(retained_imports))
    print(f"Reused verified 65-module archive sha256={digest}", flush=True)
    for name in COMMON["LOGISTIC_IMPORTS"]:
        file = Path("LongCycleBounds") / (name + ".lean")
        source = project / file
        output = (project / ".lake/build/lib/lean" / file).with_suffix(".olean")
        print(f"Compile LongCycleBounds.{name} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
        run(project, "lake", "env", "lean", "-o", str(output), str(source))


def main(project, original_log, retained_imports, continuation):
    original_log = original_log or continuation
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    upstream = (UPSTREAM, *ORIGINAL_ROOTS) if original_log else (UPSTREAM,)
    if original_log:
        run(project, "lake", "exe", "cache", "get")
    else:
        supplier = Path(*UPSTREAM.split(".")).with_suffix(".lean")
        run(project, "lake", "exe", "cache", "get", str(supplier))
    lock = json.loads((project / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        checkout = ".lake/packages/" + package["name"]
        revision = run(project, "git", "-C", checkout, "rev-parse", "HEAD", capture=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Wrong revision for {package['name']}: {revision}")
        print(f"{package['name']} {revision}", flush=True)
    build_upstream(project, upstream, retained_imports)
    build_local(project, HERE / "FourierRealAxis.lean", *REAL_AXIS)
    if original_log:
        for module in ORIGINAL_SUPPORT:
            original = HERE.parent / "common-pin" / (module + ".lean")
            build_local(project, original, module, ())
        build_local(project, HERE / "FourierOriginalLog.lean", *ORIGINAL_LOG)

    if continuation:
        module = "TiltAnalyticEvaluation"
        build_local(project, HERE.parent / "common-pin" / (module + ".lean"), module, ())
        failed = set()
        for module, theorems in CONTINUATION:
            source = HERE / (module + ".lean")
            imports = set(re.findall(r"^import ([\w.]+)", source.read_text(), re.M))
            if imports & failed:
                print(f"Skipped {module}: missing {sorted(imports & failed)}", flush=True)
                failed.add(module)
                continue
            try:
                build_local(project, source, module, theorems)
            except subprocess.CalledProcessError:
                failed.add(module)
        if failed:
            raise RuntimeError(f"Incomplete continuation checks: {sorted(failed)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a new directory for the check")
    parser.add_argument("--original-log", action="store_true", help="also check the original cutoff logarithm")
    parser.add_argument("--retained-imports", type=Path, help="verified common-pin import archive")
    parser.add_argument("--continuation", action="store_true", help="also check the original angular equation")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    if retained and not (args.original_log or args.continuation):
        parser.error("--retained-imports requires --original-log")
    main(args.project.resolve(), args.original_log, retained, args.continuation)
