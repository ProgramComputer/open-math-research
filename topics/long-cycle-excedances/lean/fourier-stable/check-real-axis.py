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
MODULE = "FourierRealAxis"
THEOREM = "OpenMathResearch.LongCycleExcedances.fourier_squared_poles_real_axis"


def main(project):
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    supplier = project / "LongCycleBounds" / "PartialFractions.lean"
    run(project, "lake", "exe", "cache", "get", str(supplier.relative_to(project)))
    lock = json.loads((project / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        checkout = ".lake/packages/" + package["name"]
        revision = run(project, "git", "-C", checkout, "rev-parse", "HEAD", capture=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Wrong revision for {package['name']}: {revision}")
        print(f"{package['name']} {revision}", flush=True)
    print(f"Compile {UPSTREAM} input-sha256={sha256(supplier.read_bytes()).hexdigest()}", flush=True)
    run(project, "lake", "--wfail", "build", "+" + UPSTREAM)
    source = project / (MODULE + ".lean")
    shutil.copyfile(HERE / source.name, source)
    output = project / ".lake" / "build" / "lib" / "lean" / (MODULE + ".olean")
    print(f"Compile {MODULE} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    audit = run(project, "lake", "env", "lean", "-DwarningAsError=true", "-o", str(output), str(source), capture=True)
    print(audit, end="", flush=True)
    match = re.findall(rf"^'{re.escape(THEOREM)}' depends on axioms:\s*\[([^\]]*)\]$", audit, re.M)
    if len(match) != 1 or {axiom.strip() for axiom in match[0].split(",")} - COMMON["ALLOWED"]:
        raise ValueError("Missing theorem or unexpected transitive axiom")
    run(project, "lake", "env", "leanchecker", "--verbose", MODULE)
    print(f"kernel_replay_exit=0 {MODULE}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a new directory for the check")
    main(parser.parse_args().project.resolve())
