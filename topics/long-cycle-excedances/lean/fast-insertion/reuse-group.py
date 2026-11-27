"""Recover an arithmetic group from a pinned and independently replayed ZIP."""
import argparse
import hashlib
import re
import runpy
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
CHECK = runpy.run_path(str(HERE / "check.py"))
PRODUCER = "0d356c3de5df643424c9a39aa0b45f0730f03081"
INSERTION = "8bd9d44b8d843664a999546d0ce3ccc91b9da83541d0570b00b68bad4a96af10"
GENERATOR = "daa51e9a86b296b5b900774c2f287ddd56a4a4e48269b2e3ae5f10a65111b2ca"
ARCHIVES = (
    (15167872990, "c2a8febcd31e7162d9ffdeea4354789ae97e38de9cdfd22933a05d09fefc0df5"),
    (15168492866, "82a67b909e17f3cb4950436fec9509608e59ebcd985b19ac7a1bfde292b82617"),
    (15168198081, "9f00205f14837bbef4a60cd034b3887a77ebea652782b2369069f3d6f2dd6c19"),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_manifest(text):
    values = {}
    for line in text.splitlines():
        sha, name = line.split("  ")
        if name in values or not re.fullmatch(r"[a-f0-9]{64}", sha):
            raise ValueError(f"Invalid manifest entry {name}")
        values[name] = sha
    return values


def recover(group, archive, output, receipt):
    artifact_id, expected_zip = ARCHIVES[group]
    if digest((HERE / "InsertionTable.lean").read_bytes()) != INSERTION:
        raise ValueError("InsertionTable no longer matches the producing build")
    if digest((HERE / "generate-checkpoints.py").read_bytes()) != GENERATOR:
        raise ValueError("Checkpoint generator no longer matches the producing build")

    with TemporaryDirectory(prefix="authenticated-insertion-") as tmp:
        work = Path(tmp)
        if archive is None:
            archive = work / "proofs.zip"
            with archive.open("wb") as target:
                subprocess.run(["gh", "api", f"repos/ProgramComputer/open-math-research/"
                                f"actions/artifacts/{artifact_id}/zip"], stdout=target, check=True)
        if digest(archive.read_bytes()) != expected_zip:
            raise ValueError("Producing artifact ZIP digest differs")
        folder = CHECK["generate"](work)
        sources = CHECK["group_sources"](folder, group)
        expected = {source.stem + ".olean" for source in sources}
        with ZipFile(archive) as zip_file:
            members = {"arithmetic.log", "row-proofs/SHA256SUMS"}
            members.update("row-proofs/" + name for name in expected)
            if len(zip_file.namelist()) != len(members) or set(zip_file.namelist()) != members:
                raise ValueError("Unexpected producing artifact ZIP inventory")
            manifest = zip_file.read("row-proofs/SHA256SUMS")
            hashes = read_manifest(manifest.decode())
            if set(hashes) != expected:
                raise ValueError("Producing proof-object manifest differs")
            log = zip_file.read("arithmetic.log")
            text = log.decode()
            if ("Lean (version 4.33.1," not in text or
                    "commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in text or
                    "mathlib 0df444a360eaa60ab8c11dca51a86af692955474" not in text):
                raise ValueError("Producing compiler or dependency pin differs")
            builds = re.findall(r"^Compile (\w+) sha256=([0-9a-f]{64})$", text, re.M)
            replays = re.findall(r"^kernel_replay_exit=0 (\w+)$", text, re.M)
            wanted = {source.stem: digest(source.read_bytes()) for source in sources}
            wanted["InsertionTable"] = INSERTION
            if (dict(builds) != wanted or len(builds) != len(wanted) or
                    set(replays) != set(wanted) or len(replays) != len(wanted)):
                raise ValueError("Producing compile and kernel reports differ")
            objects = {name: zip_file.read("row-proofs/" + name) for name in expected}
            for name, obj in objects.items():
                if digest(obj) != hashes[name]:
                    raise ValueError(f"Wrong object digest {name}")
        if output.exists() or receipt.exists():
            raise ValueError("Output or receipt already exists")
        output.mkdir(parents=True)
        for name, obj in objects.items():
            (output / name).write_bytes(obj)
        (output / "SHA256SUMS").write_bytes(manifest)
        receipt.write_bytes(log)

    print(f"Reused {len(objects)} proof objects from {PRODUCER}, artifact {artifact_id}, "
          f"sha256={expected_zip}, producer log sha256={digest(log)}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("group", type=int, choices=range(3))
    parser.add_argument("output", type=Path)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--zip", type=Path)
    args = parser.parse_args()
    try:
        recover(args.group, args.zip, args.output, args.receipt)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"No reusable producing artifact: {error}")
