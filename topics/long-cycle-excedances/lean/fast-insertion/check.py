"""Build integer endpoint proofs against the authenticated original enumerators."""

import argparse
import hashlib
import re
import runpy
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMMON = HERE.parent / "common-pin"
LEDGER = HERE.parents[1] / "intermediate/witness-ledger"
CHECKPOINT_SHA = "06ed91603ca8a9186e35efcd075aab2eb67152251007e6e8e8ac5d065b49a5ce"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT = {
    "InsertionTable": {"history_sound", "insertion_coeff", "convolution_eq", "table_agrees"},
    "RoundedHorner": {"roundedRatio_eq", "rounded_error", "signed_lower", "horner_first"},
    "IntegerTail": {"integer_tail_margin"},
    "OriginalInsertionSigns": {"enumerator_empty", "insertionEulerian_agrees",
                               "original_insertion_table", "original_signed_point_of_rounded_prefix",
                               "original_signed_of_integer_check"},
    "CheckedShard": {"check_sound", "checkedShard"},
    "CheckpointReplay": {"checkpoint_step0", "checkpoint_step251", "checkpoint_first_pair"},
    "FirstPairChecks": {"firstPairRanks"},
    "FirstPairModel": {"firstPairOldAgrees", "firstPairNewAgrees"},
    "FirstPairArithmetic": {"firstPairAllChecks"},
    "FirstPairOriginal": {"firstPair_original_signs"},
}


def compile_module(project, module, expected):
    source = project / (module + ".lean")
    output = project / ".lake/build/lib/lean" / (module + ".olean")
    print(f"Compile {module} sha256={hashlib.sha256(source.read_bytes()).hexdigest()}", flush=True)
    result = subprocess.run(["lake", "env", "lean", "-j1", "-DwarningAsError=true", "-o", str(output),
                             str(source)], cwd=project, text=True, capture_output=True)
    print(result.stdout, result.stderr, end="", flush=True)
    result.check_returncode()
    observed = set()
    for name, axioms in re.findall(
        r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
        result.stdout, flags=re.M,
    ):
        used = {v.strip() for v in axioms.split(",") if v.strip()}
        if used - ALLOWED:
            raise ArithmeticError(f"Unexpected axioms for {name}: {used}")
        observed.add(name.rsplit(".", 1)[-1])
    if expected - observed:
        raise ArithmeticError(f"Missing axiom reports for {expected - observed}")
    subprocess.run(["lake", "env", "leanchecker", "--verbose", module.replace("/", ".")],
                   cwd=project, check=True)
    print(f"kernel_replay_exit=0 {module}", flush=True)


def prepare_arithmetic(project):
    common = runpy.run_path(str(COMMON / "check.py"))
    run = common["run"]
    project.mkdir(parents=True)
    common["prepare"](project)
    version = run(project, "lean", "--version", capture=True).strip()
    if common["COMPILER"] not in version:
        raise ValueError(version)
    print(version, flush=True)
    run(project, "lake", "exe", "cache", "get")
    revision = run(project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD",
                   capture=True).strip()
    if common["MATHLIB"] != revision:
        raise ValueError(revision)
    print(f"mathlib {revision}", flush=True)


def source_module(project, source):
    shutil.copyfile(source, project / source.name)
    name = source.stem
    expected = AUDIT.get(name, set())
    if name.startswith("FirstPairChecks") and name != "FirstPairChecks":
        expected = {"firstPairBlock" + name.removeprefix("FirstPairChecks")}
    compile_module(project, name, expected)


def generate(project):
    folder = project / "generated-checkpoints"
    subprocess.run([sys.executable, str(HERE / "generate-checkpoints.py"), str(folder)], check=True)
    if hashlib.sha256((folder / "SHA256SUMS").read_bytes()).hexdigest() != CHECKPOINT_SHA:
        raise ValueError("Generated coefficient checkpoint manifest changed")
    subprocess.run(["sha256sum", "--quiet", "-c", "SHA256SUMS"], cwd=folder, check=True)
    return folder


def group_sources(folder, group):
    chunks = sorted(folder.glob("CheckpointChunk*.lean"))
    if len(chunks) != 42:
        raise ValueError("Expected 42 six-equation modules")
    chunks = chunks[group * 14:(group + 1) * 14]
    dependencies = set()
    for chunk in chunks:
        dependencies.update(re.findall(r"^import (CheckpointData[0-9]+)$", chunk.read_text(), re.M))
    return [folder / (module + ".lean") for module in sorted(dependencies)] + chunks


def check_group(project, group, output):
    prepare_arithmetic(project)
    (project / ".lake/build/lib/lean").mkdir(parents=True, exist_ok=True)
    source_module(project, HERE / "InsertionTable.lean")
    folder = generate(project)
    output.mkdir(parents=True, exist_ok=True)
    manifest = []
    for source in group_sources(folder, group):
        source_module(project, source)
        name = source.stem + ".olean"
        shutil.copyfile(project / ".lake/build/lib/lean" / name, output / name)
        digest = hashlib.sha256((output / name).read_bytes()).hexdigest()
        manifest.append(f"{digest}  {name}\n")
    (output / "SHA256SUMS").write_text("".join(manifest))


def recover_groups(project, folder, groups):
    for group in range(3):
        inputs = groups / f"row-proofs-{group}"
        sources = group_sources(folder, group)
        expected = {source.stem + ".olean" for source in sources}
        if {path.name for path in inputs.glob("*.olean")} != expected:
            raise ValueError(f"Missing or unexpected proof objects for group {group}")
        names = set()
        for line in (inputs / "SHA256SUMS").read_text().splitlines():
            digest, name = line.split("  ")
            if name not in expected or name in names:
                raise ValueError(f"Invalid manifest entry {name}")
            source = inputs / name
            if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
                raise ValueError(f"Wrong object digest for {name}")
            names.add(name)
            target = project / ".lake/build/lib/lean" / name
            if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() != digest:
                raise ValueError(f"Independent builds disagree for {name}")
            shutil.copyfile(source, target)
        if names != expected:
            raise ValueError(f"Incomplete manifest for group {group}")
        print(f"Recovered {len(sources)} checked modules from group {group}", flush=True)


def main(project, imports, groups=None):
    runpy.run_path(str(COMMON / "check.py"))["main"](project, imports)
    compile_module(project, "LongCycleBounds/UniversalRecurrence", set())
    for module in ("InsertionTable", "RoundedHorner", "IntegerTail", "CheckedShard", "OriginalInsertionSigns"):
        source_module(project, (LEDGER if module == "CheckedShard" else HERE) / (module + ".lean"))
    folder = generate(project)
    if groups is None:
        for source in sorted(folder.glob("CheckpointData*.lean")) + sorted(folder.glob("CheckpointChunk*.lean")):
            source_module(project, source)
    else:
        recover_groups(project, folder, groups)
    source_module(project, folder / "CheckpointReplay.lean")
    for module in ("FirstPairModel", "FirstPairChecks", "FirstPairChecks0", "FirstPairChecks6",
                   "FirstPairChecks12", "FirstPairChecks18", "FirstPairChecks24",
                   "FirstPairArithmetic", "FirstPairOriginal"):
        source_module(project, HERE / (module + ".lean"))
    print("PASS: original permutation signs for 26 gaps, 2 rows, 2 endpoints", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("imports", nargs="?", type=Path)
    parser.add_argument("--group", choices=range(3), type=int)
    parser.add_argument("--objects", type=Path)
    parser.add_argument("--groups", type=Path)
    args = parser.parse_args()
    if args.group is None:
        main(args.project.resolve(), args.imports.resolve() if args.imports else None, args.groups)
    else:
        if args.objects is None:
            parser.error("--group requires --objects")
        check_group(args.project.resolve(), args.group, args.objects.resolve())
