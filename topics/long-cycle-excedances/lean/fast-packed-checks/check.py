"""Run the pinned packed endpoint and row storage benchmarks."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy
import subprocess
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent
ENDPOINT = runpy.run_path(str(HERE.parent / "packed-endpoints/check.py"))
AUDIT = ENDPOINT["COMPACT"]["audit_module"]


def check(project, imports):
    ENDPOINT["check"](project, imports)
    output = project / "generated-fast-packed-checks"
    subprocess.run([sys.executable, "-B", str(HERE / "generate.py"), str(output)], check=True)

    def audit(folder, module, *expected):
        source = folder / (module + ".lean")
        start = perf_counter()
        AUDIT(project, module, set(expected), source)
        obj = project / ".lake/build/lib/lean" / (module + ".olean")
        print(f"Benchmark {module} seconds={perf_counter()-start:.3f} "
              f"source_bytes={source.stat().st_size} olean_bytes={obj.stat().st_size} "
              f"source_sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)

    audit(HERE, "CoarseTail", "coarse_geometric_tail")
    audit(HERE, "CoarseCheck", "coarse_integer_margin", "packed_check_of_coarse")
    audit(HERE, "FastPackedPoint", "pairedHorner_eq", "fastCoarseCheck_eq")
    audit(HERE, "RepositoryFastPackedPoint", "original_signed_of_fast_packed_words")
    audit(HERE, "HighSizePoint", "signedAt_of_check")
    audit(output, "HighSizeData")
    audit(HERE, "HighSizeAudit", "checks51", "checks160", "high_size_51_original",
          "high_size_160_original")
    audit(HERE, "SharpControl", "control51", "control160")

    audit(HERE, "RowWordStorage", "unpackWordRow_packWordRow")
    audit(HERE.parent / "packed-shard", "PackedRowCore", "wordOK_sound", "packedTable_sound")
    audit(output, "PackedRowData", "packedRow_seed")
    audit(output, "PackedWordData", "packedRow_seed")
    audit(HERE, "StorageAudit", "listLastStep", "packedLastStep")
    print("PASS: 88 high-size endpoint checks with original-row transfer, and packed storage round-trip.",
          flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("imports", type=Path, nargs="?")
    args = parser.parse_args()
    check(args.project.resolve(), args.imports.resolve() if args.imports else None)
