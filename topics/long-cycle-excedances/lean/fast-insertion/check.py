"""Build integer endpoint proofs against the authenticated original enumerators."""

import argparse
import hashlib
import json
import os
import re
import runpy
import shutil
import signal
import subprocess
import sys
from zipfile import ZipFile
from pathlib import Path
from time import monotonic

HERE = Path(__file__).resolve().parent
COMMON = HERE.parent / "common-pin"
LEDGER = HERE.parents[1] / "intermediate/witness-ledger"
CHECKPOINT_SHA = "06ed91603ca8a9186e35efcd075aab2eb67152251007e6e8e8ac5d065b49a5ce"
CHILD_SECONDS = 300
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
    "FirstPairEulerian": {"descentCoeffsSnapshot12"},
    "FirstPairWeights": {"firstPairWeights", "firstPairWeightAgrees"},
    "FirstPairRecurrence": {"firstPairSuccessor"},
    "FirstPairModel": {"firstPairOriginal"},
    "FirstPairAgreement": {"firstPair_agreement"},
    "FirstPairArithmetic": {"firstPairAllChecks"},
    "FirstPairOriginal": {"firstPair_original_signs"},
}


def linux_memory_limit():
    """Keep a reserve for the runner and its logging process."""
    if sys.platform != "linux":
        return None
    info = Path("/proc/meminfo").read_text()
    limits = [1024 * int(re.search(r"^MemTotal:\s+(\d+)", info, re.M)[1])]
    for path in (Path("/sys/fs/cgroup/memory.max"),
                 Path("/sys/fs/cgroup/memory/memory.limit_in_bytes")):
        if path.is_file():
            value = path.read_text().strip()
            if value.isdecimal():
                limits.append(int(value))
    available = min(limits)
    return min(available * 3 // 4, available - 1024**3)


def process_group_rss(group):
    rows = subprocess.check_output(["ps", "-eo", "pgid=,rss="], text=True, timeout=5)
    return sum(int(rss) * 1024 for pgid, rss in
               (row.split() for row in rows.splitlines() if row.strip())
               if int(pgid) == group)


def run_lean(project, name, argv):
    limit = linux_memory_limit()
    if limit is not None and limit <= 0:
        raise RuntimeError(f"Not enough runner memory for {name}: cap {limit} bytes")
    with subprocess.Popen(argv, cwd=project, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, start_new_session=True) as child:
        deadline = monotonic() + CHILD_SECONDS
        while True:
            try:
                log, _ = child.communicate(timeout=1)
                break
            except subprocess.TimeoutExpired:
                cause = None
                if monotonic() >= deadline:
                    cause = f"exceeded {CHILD_SECONDS} seconds"
                elif limit is not None:
                    try:
                        rss = process_group_rss(child.pid)
                        if rss > limit:
                            cause = f"reached {rss} resident bytes (cap {limit})"
                    except (OSError, subprocess.SubprocessError, ValueError) as error:
                        cause = f"could not check resident memory: {error}"
                if cause is None:
                    continue
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                log, _ = child.communicate()
                print(log, end="", flush=True)
                raise RuntimeError(f"{name} {cause}")
        print(log, end="", flush=True)
        if child.returncode:
            raise RuntimeError(f"{name} exited {child.returncode}")
    return log


def compile_module(project, module, expected):
    source = project / (module + ".lean")
    output = project / ".lake/build/lib/lean" / (module + ".olean")
    print(f"Compile {module} sha256={hashlib.sha256(source.read_bytes()).hexdigest()}", flush=True)
    log = run_lean(project, f"compile {module}",
                   ["lake", "env", "lean", "-j1", "-DwarningAsError=true", "-o", str(output), str(source)])
    observed = set()
    for name, axioms in re.findall(
        r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
        log, flags=re.M,
    ):
        used = {v.strip() for v in axioms.split(",") if v.strip()}
        if used - ALLOWED:
            raise ArithmeticError(f"Unexpected axioms for {name}: {used}")
        observed.add(name.rsplit(".", 1)[-1])
    if expected - observed:
        raise ArithmeticError(f"Missing axiom reports for {expected - observed}")
    run_lean(project, f"replay {module}",
             ["lake", "env", "leanchecker", "--verbose", module.replace("/", ".")])
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


PAIR_CACHE_SHA = "e3aa4ee98052400944a2376317131425a37df1579d155ecf25f81b87cb3998fd"
PAIR_CACHE_HEAD = "fff20d6964bdacd586c481a75f4426a4d5ac6306"
PAIR_CACHE_MODULES = (
    "FirstPairEulerian", "FirstPairWeights", "FirstPairChecks", "FirstPairChecks0",
    "FirstPairChecks6", "FirstPairChecks12", "FirstPairChecks18", "FirstPairChecks24",
    "FirstPairArithmetic",
)
PAIR_CACHE_DEPENDENCIES = {
    "InsertionTable": "8bd9d44b8d843664a999546d0ce3ccc91b9da83541d0570b00b68bad4a96af10",
    "RoundedHorner": "024c1645e91a8e54d1a9e563117b784e7f974c689cd36d9249940875109eb02c",
    "IntegerTail": "54087397cba42da15554f17b06e973774656903b865ef1b5f3f311d5d71b6742",
    "OriginalInsertionSigns": "8c54c1cc715d952f63b1109a04583617461c4cbe420aeefd76d730cb2c26b3a8",
    "CheckedShard": "592ba9cb6edd37fae2d097672b6403329ecb6bd9621f4d938240f981061eba0e",
    "CheckpointReplay": "54759a29a4e5fd15347380893acfe248dcb867da6a87937b19bc17cc25f76a6f",
}


def read_pair_cache(project, archive):
    if hashlib.sha256(archive.read_bytes()).hexdigest() != PAIR_CACHE_SHA:
        raise ValueError("First-pair artifact ZIP digest differs")
    for name, digest in PAIR_CACHE_DEPENDENCIES.items():
        if hashlib.sha256((project / (name + ".lean")).read_bytes()).hexdigest() != digest:
            raise ValueError(f"First-pair dependency {name} differs")
    cache = {}
    with ZipFile(archive) as z:
        expected = {f"{name}/{leaf}" for name in PAIR_CACHE_MODULES
                    for leaf in (name + ".olean", "receipt.json")}
        if len(z.namelist()) != len(expected) or set(z.namelist()) != expected:
            raise ValueError("First-pair artifact ZIP inventory differs")
        for name in PAIR_CACHE_MODULES:
            proof = z.read(f"{name}/{name}.olean")
            receipt = z.read(f"{name}/receipt.json")
            expected_receipt = {
                "module": name,
                "source_head": PAIR_CACHE_HEAD,
                "witness_shard_sha256": PAIR_CACHE_DEPENDENCIES["CheckedShard"],
                "source_sha256": hashlib.sha256((HERE / (name + ".lean")).read_bytes()).hexdigest(),
                "olean_sha256": hashlib.sha256(proof).hexdigest(),
                "checkpoint_manifest_sha256": CHECKPOINT_SHA,
                "compiler": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
                "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
                "kernel_replay_exit": 0,
            }
            if json.loads(receipt) != expected_receipt:
                raise ValueError(f"First-pair receipt for {name} differs")
            cache[name] = (proof, receipt)
    return cache


def install_pair_object(project, output, name, cached):
    proof, receipt = cached
    (project / ".lake/build/lib/lean" / (name + ".olean")).write_bytes(proof)
    if output is not None:
        dest = output / name
        dest.mkdir(parents=True)
        (dest / (name + ".olean")).write_bytes(proof)
        (dest / "receipt.json").write_bytes(receipt)
    print(f"Reused authenticated and already replayed module {name}", flush=True)


def preserve_module(project, output, module):
    source = project / (module + ".lean")
    obj = project / ".lake/build/lib/lean" / (module + ".olean")
    folder = output / module
    folder.mkdir(parents=True)
    shutil.copyfile(obj, folder / obj.name)
    receipt = {
        "module": module,
        "source_head": subprocess.check_output(
            ["git", "-C", str(HERE), "rev-parse", "HEAD"], text=True
        ).strip(),
        "witness_shard_sha256": hashlib.sha256((LEDGER / "CheckedShard.lean").read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "olean_sha256": hashlib.sha256(obj.read_bytes()).hexdigest(),
        "checkpoint_manifest_sha256": CHECKPOINT_SHA,
        "compiler": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
        "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
        "kernel_replay_exit": 0,
    }
    (folder / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


def main(project, imports, groups=None, pair_objects=None, pair_cache=None):
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
    cached = {}
    if pair_cache is not None and imports is not None:
        try:
            cached = read_pair_cache(project, pair_cache)
        except (OSError, ValueError) as error:
            print(f"No reusable first-pair objects: {error}", flush=True)
    for module in (*PAIR_CACHE_MODULES, "FirstPairRecurrence", "FirstPairModel",
                   "FirstPairAgreement", "FirstPairOriginal"):
        if module in cached:
            install_pair_object(project, pair_objects, module, cached[module])
        else:
            source_module(project, HERE / (module + ".lean"))
            if pair_objects is not None:
                preserve_module(project, pair_objects, module)
    print("PASS: original permutation signs for 26 gaps, 2 rows, 2 endpoints", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("imports", nargs="?", type=Path)
    parser.add_argument("--group", choices=range(3), type=int)
    parser.add_argument("--objects", type=Path)
    parser.add_argument("--groups", type=Path)
    parser.add_argument("--pair-objects", type=Path)
    parser.add_argument("--pair-cache", type=Path)
    args = parser.parse_args()
    if args.group is None:
        main(args.project.resolve(), args.imports.resolve() if args.imports else None, args.groups, args.pair_objects, args.pair_cache)
    else:
        if args.objects is None:
            parser.error("--group requires --objects")
        check_group(args.project.resolve(), args.group, args.objects.resolve())
