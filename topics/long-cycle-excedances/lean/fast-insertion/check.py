"""Build integer endpoint proofs against the authenticated original enumerators."""

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
CHECKPOINT_SHA = "6d80035f444ca9147c4236c777215eb374fe0322e992df67a1fbfc2c38cc73d5"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT = {
    "InsertionTable": {"history_sound", "insertion_coeff", "table_agrees"},
    "RoundedHorner": {"roundedRatio_eq", "rounded_error", "signed_lower", "horner_first"},
    "IntegerTail": {"integer_tail_margin"},
    "OriginalInsertionSigns": {"enumerator_empty", "insertionEulerian_agrees",
                               "original_insertion_table", "original_signed_point_of_rounded_prefix",
                               "original_signed_of_integer_check"},
    "CheckedShard": {"check_sound", "checkedShard"},
    "CheckpointReplay": {"checkpoint_step0", "checkpoint_step251", "checkpoint_first_pair"},
    "FirstPairOriginal": {"firstPairRanks", "firstPairAllChecks", "firstPair_original_signs"},
}


def compile_module(project, module, expected):
    source = project / (module + ".lean")
    output = project / ".lake/build/lib/lean" / (module + ".olean")
    print(f"Compile {module} sha256={hashlib.sha256(source.read_bytes()).hexdigest()}", flush=True)
    result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "-o", str(output),
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


def main(project, imports):
    runpy.run_path(str(COMMON / "check.py"))["main"](project, imports)
    compile_module(project, "LongCycleBounds/UniversalRecurrence", set())
    passed = set()
    for module in ("InsertionTable", "RoundedHorner", "IntegerTail", "CheckedShard"):
        source = project / (module + ".lean")
        shutil.copyfile((LEDGER if module == "CheckedShard" else HERE) / source.name, source)
        try:
            compile_module(project, module, AUDIT[module])
        except (subprocess.CalledProcessError, ArithmeticError) as error:
            print(error, flush=True)
        else:
            passed.add(module)
    if len(passed) != 4:
        raise ArithmeticError(f"Foundational modules passing: {sorted(passed)}")
    for module, expected in AUDIT.items():
        if module in passed:
            continue
        source = project / (module + ".lean")
        if module == "CheckpointReplay":
            folder = project / "generated-checkpoints"
            subprocess.run([sys.executable, str(HERE / "generate-checkpoints.py"), str(folder)],
                           check=True)
            if hashlib.sha256((folder / "SHA256SUMS").read_bytes()).hexdigest() != CHECKPOINT_SHA:
                raise ValueError("Generated coefficient checkpoint manifest changed")
            subprocess.run(["sha256sum", "--quiet", "-c", "SHA256SUMS"], cwd=folder, check=True)
            for part in sorted(folder.glob("CheckpointChunk*.lean")):
                shutil.copyfile(part, project / part.name)
                compile_module(project, part.stem, set())
            shutil.copyfile(folder / source.name, source)
        else:
            shutil.copyfile((LEDGER if module == "CheckedShard" else HERE) / source.name, source)
        compile_module(project, module, expected)
    print("PASS: original permutation signs for 26 gaps, 2 rows, 2 endpoints", flush=True)


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None)
