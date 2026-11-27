"""Rebuild the supplying cutoff-seven release and a lower-size comparison."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import urllib.request
from zipfile import ZipFile

COMMIT = "84418bbac7f071f49394c9dc297501671e1a2052"
BASE = "https://raw.githubusercontent.com/AlexZander-666/long-cycle-excedance-interlacing/"
SOURCE = BASE + COMMIT + "/cutoff-seven/formal/cutoff-seven-all-source.zip"
SOURCE_HASH = "acbc05bf6119e341714756e5f42a1b37ef3ccc339be67c536dff6bb14632154b"
LOCK_HASH = "e33edc324af4940c42846f10e6a919ce3bd62abb219a2955a5644b3a936cfc19"
LEAN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"


def verify_hash(data, expected):
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("frozen source or dependency hash mismatch")


def prepare(directory):
    directory.mkdir(parents=True)
    with urllib.request.urlopen(SOURCE, timeout=60) as reply:
        data = reply.read()
    verify_hash(data, SOURCE_HASH)
    with ZipFile(io.BytesIO(data)) as archive:
        for name in archive.namelist():
            if Path(name).is_absolute() or ".." in Path(name).parts:
                raise ValueError(f"invalid archive member {name}")
        archive.extractall(directory)
    subprocess.run(["shasum", "-a", "256", "--quiet", "-c", "SHA256SUMS"],
                   cwd=directory, check=True)
    manifest = (directory / "lake-manifest.json").read_bytes()
    verify_hash(manifest, LOCK_HASH)
    packages = json.loads(manifest)["packages"]
    assert any(p["name"] == "mathlib" and p["rev"] == MATHLIB for p in packages)
    assert (directory / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    shutil.copyfile(Path(__file__).with_name("OriginalClaim.lean"), directory / "OriginalClaim.lean")
    supplied_audit = (directory / "SevenCutoffAudit.lean").read_text()
    (directory / "CombinedAudit.lean").write_text(
        "import OriginalClaim\n" + supplied_audit +
        "\n#print LongCycles.Allowed\n#print LongCycles.excedances\n#print LongCycles.enumerator\n"
        "#print LongCycleFinite.StrictNegativeInterlacing\n#print LongCycles.WeakRealInterlacing\n"
        "#check @LongCycleBounds.SevenCutoff.all_sizes\n#check @IndependentCutoffSeven.from_lower_size\n"
        "#print axioms IndependentCutoffSeven.from_lower_size\n")
    print(f"Source {SOURCE}\nSHA256 {SOURCE_HASH}\nLock {LOCK_HASH}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fresh_directory", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    project = args.fresh_directory.resolve()
    prepare(project)
    if not args.source_only:
        version = subprocess.check_output(["lean", "--version"], cwd=project, text=True).strip()
        if LEAN not in version:
            raise ValueError(f"unexpected Lean compiler {version}")
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        subprocess.run([sys.executable, "-Bu", "verify_lean.py", str(project), "CombinedAudit",
                        "--jobs", "2"], cwd=project, check=True, env=env)
