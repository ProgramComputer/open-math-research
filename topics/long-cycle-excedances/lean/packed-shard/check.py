"""Build and replay the first original packed-word endpoint shard."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEDGER = HERE.parents[1] / "intermediate" / "witness-ledger"
ENDPOINT = runpy.run_path(str(HERE.parent / "packed-endpoints" / "check.py"))
AUDIT = ENDPOINT["COMPACT"]["audit_module"]
GENERATED_SHA = "7d63ed4b0e3020d922d3fad5be8802cad225f4ec6253d5cf82c16fa6f7305f71"


def audit_leaves(project, folder, workers):
    sources = []
    for path in sorted(folder.glob("PackedSteps*.lean")):
        start = int(path.stem.removeprefix("PackedSteps"))
        sources.append((path, {f"packedSteps{start}"}))
    for path in sorted(folder.glob("PackedEndpoints*.lean")):
        old_size = int(path.stem.removeprefix("PackedEndpoints"))
        sources.append((path, {f"checks{old_size}"}))
    if len(sources) != 26:
        raise ValueError("Unexpected certificate module count")
    failures = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        pending = {pool.submit(AUDIT, project, path.stem, expected, path): path.stem
                   for path, expected in sources}
        for future in as_completed(pending):
            try:
                future.result()
            except (subprocess.CalledProcessError, ValueError) as error:
                print(f"Module failed: {pending[future]}: {error}", flush=True)
                failures.append(pending[future])
    if failures:
        raise RuntimeError(f"Certificate modules failed: {', '.join(sorted(failures))}")


def check(project, imports, workers):
    ENDPOINT["check"](project, imports)
    folder = project / "generated-packed-shard"
    subprocess.run([sys.executable, "-B", str(HERE / "generate-packed-shard.py"),
                    str(folder), str(LEDGER / "shard.csv")], check=True)
    manifest = folder / "SHA256SUMS"
    if hashlib.sha256(manifest.read_bytes()).hexdigest() != GENERATED_SHA:
        raise ValueError("Packed data or generated module manifest changed")
    subprocess.run(["sha256sum", "--quiet", "-c", manifest.name], cwd=folder, check=True)

    AUDIT(project, "CheckedShard", {"check_sound", "checkedShard"}, LEDGER / "CheckedShard.lean")
    AUDIT(project, "PackedRowCore", {"wordOK_sound", "fastValue_eq", "packedTable_sound"},
          HERE / "PackedRowCore.lean")
    AUDIT(project, "PackedRowData", {"packedRow_seed"}, folder / "PackedRowData.lean")
    AUDIT(project, "PackedShardTest", {"checkedShard_card", "shard_supported"},
          HERE / "PackedShardTest.lean")
    audit_leaves(project, folder, workers)
    AUDIT(project, "PackedRowSteps", {"packedSteps"}, folder / "PackedRowSteps.lean")
    AUDIT(project, "PackedShardChecks", {"shard_gapOK"}, HERE / "PackedShardChecks.lean")
    AUDIT(project, "PackedShardOriginal", {"packedShard_row", "firstShard_original_signs"},
          HERE / "PackedShardOriginal.lean")
    print("PASS: 131 gaps and 524 strict signs for the original permutation quotients.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the frozen Lean project")
    parser.add_argument("imports", type=Path, nargs="?", help="authenticated import objects")
    parser.add_argument("--jobs", type=int, choices=(1, 2, 3), default=2)
    args = parser.parse_args()
    check(args.project.resolve(), args.imports.resolve() if args.imports else None, args.jobs)
