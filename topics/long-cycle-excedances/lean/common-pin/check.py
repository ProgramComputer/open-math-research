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
EXPECTED = {
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
                   "OpenMathResearch.FirstLevelHits", "LongCyclePhaseWindows", "RepositoryPoleProfile"):
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
    compile_topic(project)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
