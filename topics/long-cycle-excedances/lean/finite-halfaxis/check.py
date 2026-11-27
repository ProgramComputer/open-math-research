#!/usr/bin/env python3
"""Check the first original adjacent pair in the compact cutoff-eight archive."""

import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy
import shutil
import urllib.request

HERE = Path(__file__).resolve().parent
TOPIC = HERE.parent
COMPACT = runpy.run_path(str(TOPIC / "compact-rows" / "check.py"))
COMMON = COMPACT["COMMON"]
AUDIT = COMPACT["audit_module"]
PIN = "4c3b59180061259183d4469552a2f375986e119c"
ARCHIVE = "topics/long-cycle-excedances/finite-prefix/dyadic-windows/k8-n32-250.jsonl.gz"
ARCHIVE_SHA = "95f445fa4e7864984c33ca44eb2f83a8295a628721e0b65bf523fb55265490e8"
COMMON_INPUTS = (
    "RationalPointSound", "RepositoryQuotientShape", "RepositoryActualRationalPoint",
    "StrictRootListTranslation", "RepositoryRootAssembly", "ReciprocalWindowSigns",
    "ReciprocalHalfWindows", "RepositoryHalfAxisAssembly",
)
TOPIC_INPUTS = ("LongCyclePhaseWindows", "LongCycleMixedRootWitnesses", "LongCyclePrefixTail",
                "LongCycleRunColors", "LongCycleReducedRow")
MODULES = {
    "ExactInsertionTable": {"exactListTable_reads", "ofCoeffs_eq_original_of_reads"},
    "RepositoryStrictHalfWindows": {"original_strict_and_weak_of_half_axis_windows"},
    "HalfAxisDyadic": {"original_strict_and_weak_of_checked_half_axis"},
    "HalfAxisBlock": {"original_strict_and_weak_block_of_checked_half_axis"},
    "CutoffEightRows": {"rows_original"},
    "CutoffEightFirstPair": {"original_strict_and_weak_cutoff8_size32"},
}


def verify_fixture():
    path = HERE.parents[3] / ARCHIVE
    if path.is_file():
        raw = gzip.decompress(path.read_bytes())
    else:
        url = f"https://raw.githubusercontent.com/ProgramComputer/open-math-research/{PIN}/{ARCHIVE}"
        with urllib.request.urlopen(url, timeout=45) as response:
            raw = gzip.decompress(response.read())
    if sha256(raw).hexdigest() != ARCHIVE_SHA:
        raise ValueError("Unexpected uncompressed certificate digest")
    entries = [json.loads(line) for line in raw.splitlines()[:15]]
    source = (HERE / "CutoffEightFirstPair.lean").read_text()
    literals = re.findall(r"^  \| (\d+|_) => ⟨⟨(\d+), (\d+)⟩, ⟨(\d+), (\d+)⟩⟩$", source, re.M)
    if [entry[:2] for entry in entries] != [[32, i] for i in range(15)]:
        raise ValueError("Unexpected fixture row or window index")
    expected = [(str(i) if i < 14 else "_", str(a), str(e), str(b), str(f))
                for _, i, a, e, b, f in entries]
    if len(expected) != 15 or expected != literals:
        raise ValueError("Lean window literals differ from checked archive")
    print(f"Verified 15 stored brackets against #331 sha256={ARCHIVE_SHA}", flush=True)


def check(project, imports):
    verify_fixture()
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    version = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in version:
        raise ValueError(f"Unexpected compiler: {version}")
    print(version, flush=True)
    run(project, "lake", "exe", "cache", "get")
    lock = json.loads((project / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        checkout = ".lake/packages/" + package["name"]
        revision = run(project, "git", "-C", checkout, "rev-parse", "HEAD", capture=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Wrong dependency revision: {package['name']} {revision}")
        print(f"{package['name']} {revision}", flush=True)
    if imports is None:
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient",
            "+LongCycleBounds.UniversalRecurrence", "+LongCycleFinite.CoefficientRows",
            "+LongCycleFinite.Rounded", "+LongCycleFinite.Assembly")
    else:
        digest = sha256(imports.read_bytes()).hexdigest()
        if digest != COMMON["IMPORT_SHA"]:
            raise ValueError(f"Unexpected import archive: {digest}")
        run(project, "tar", "--zstd", "-xf", str(imports))
        print(f"Authenticated import objects sha256={digest}", flush=True)
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.UniversalRecurrence")
    def stage(source, module):
        target = project / (module + ".lean")
        out = project / ".lake/build/lib/lean" / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        print(f"Compile {module} sha256={sha256(target.read_bytes()).hexdigest()}", flush=True)
        run(project, "lake", "env", "lean", "-o", str(out), str(target))

    shared = COMMON["SHARED"] / "OpenMathResearch"
    for name in ("FirstLevelHits", "AlternatingSignRoots", "OrientedNegativeInterlace", "DiskUniqueness"):
        stage(shared / (name + ".lean"), "OpenMathResearch/" + name)
    for name in TOPIC_INPUTS:
        stage(TOPIC / (name + ".lean"), name)
    stage(TOPIC / "pinned-quotient" / "RepositoryQuotientAdapter.lean", "RepositoryQuotientAdapter")
    for name in COMMON_INPUTS:
        stage(TOPIC / "common-pin" / (name + ".lean"), name)
    for name, theorems in COMPACT["AUDITS"].items():
        AUDIT(project, name, theorems, TOPIC / "compact-rows" / (name + ".lean"))
    for name, theorems in MODULES.items():
        AUDIT(project, name, theorems, HERE / (name + ".lean"))
    print("PASS: original cutoff-eight adjacent pair n=32,33 checked", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("imports", type=Path, nargs="?")
    args = parser.parse_args()
    check(args.project.resolve(), args.imports.resolve(strict=True) if args.imports else None)
