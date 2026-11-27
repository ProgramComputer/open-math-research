"""Check the rounding bound for the literal minimum-cycle permutation rows."""

import argparse
import re
import runpy
import shutil
import subprocess
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMMON = runpy.run_path(str(HERE.parent / "common-pin/check.py"))
AUDITS = {
    "TruncatedRows": {"chop_loss", "all_rows_within", "uniform_error_factor", "signed_prefix_error"},
    "CompactRowModel": {"lowerRows_succ", "decode_encode", "encode_fits", "word_fits_envelope"},
    "OriginalRoundedRows": {"originalReducedCount_eq", "originalReducedCount_short",
                            "original_count_step", "rounded_counts_within"},
    "RepositoryCompactRows": {"compact_seed_count", "compact_all_original",
                              "compact_original_prefix_error"},
}


def audit_module(project, module, expected, source_path=None):
    source = project / (module + ".lean")
    output = project / ".lake/build/lib/lean" / (module + ".olean")
    if source_path is not None:
        shutil.copyfile(source_path, source)
    print(f"Compile {module} sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    command = ["lake", "env", "lean", "-DwarningAsError=true", "-o",
               str(output), str(source)]
    result = subprocess.run(command, cwd=project, text=True, capture_output=True)
    print(result.stdout, result.stderr, sep="", end="", flush=True)
    result.check_returncode()
    seen = set()
    for name, group in re.findall(
        r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",
        result.stdout, flags=re.M,
    ):
        axioms = {word.strip() for word in group.split(",") if word.strip()}
        if axioms - COMMON["ALLOWED"]:
            raise ValueError(f"Unexpected axioms for {name}: {axioms}")
        seen.add(name.rsplit(".", 1)[-1])
    missing = expected - seen
    if missing:
        raise ValueError(f"Missing theorem audits for {missing}")
    COMMON["run"](project, "lake", "env", "leanchecker", "--verbose", module.replace("/", "."))
    print(f"kernel_replay_exit=0 {module}", flush=True)


def check(project, imports):
    COMMON["main"](project, imports)
    audit_module(project, "LongCycleBounds/UniversalRecurrence", set())
    for module, expected in AUDITS.items():
        audit_module(project, module, expected, HERE / (module + ".lean"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new working directory")
    parser.add_argument("imports", type=Path, nargs="?", help="authenticated object archive")
    args = parser.parse_args()
    check(args.project.resolve(), args.imports.resolve() if args.imports else None)
