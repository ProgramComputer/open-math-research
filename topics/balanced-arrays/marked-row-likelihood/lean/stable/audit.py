"""Stage and audit the two marked-row modules with the stable publication pins."""
import argparse
import hashlib
import json
import re
import runpy
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PUBLICATION = ROOT / "shared/lean/publication"
MODULES = ("MarkedPairing", "ArrayOrientation")
AUDIT_COMMAND = re.compile(r"(?m)^#print axioms ([\w.]+)$")


def stage(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copyfile(PUBLICATION / name, directory / name)
    manifest = json.loads((directory / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    lakefile = [
        'name = "marked_row_stable"',
        "",
        "[[require]]",
        'name = "mathlib"',
        f'scope = "{mathlib["scope"]}"',
        f'git = "{mathlib["url"]}"',
        f'rev = "{mathlib["rev"]}"',
    ]
    imports = set()
    sources = {}
    for name in MODULES:
        original = HERE.parent / f"{name}.lean"
        staged = directory / original.name
        shutil.copyfile(original, staged)
        port = HERE / f"{name}.patch"
        if port.is_file():
            subprocess.run(["patch", "--fuzz=0", "-s", str(staged), str(port)], check=True)
        imports.update(re.findall(r"(?m)^import (Mathlib\.[\w.]+)$", staged.read_text()))
        sources[name] = {
            "path": str(original.relative_to(ROOT)),
            "source_sha256": hashlib.sha256(original.read_bytes()).hexdigest(),
            "staged_sha256": hashlib.sha256(staged.read_bytes()).hexdigest(),
        }
        lakefile.extend(["", "[[lean_lib]]", f'name = "{name}"'])
    (directory / "lakefile.toml").write_text("\n".join(lakefile) + "\n")
    (directory / "cache-imports.txt").write_text("\n".join(sorted(imports)) + "\n")
    (directory / "sources.json").write_text(json.dumps(sources, indent=2) + "\n")


def audit(directory):
    parse_output = runpy.run_path(str(PUBLICATION / "audit_axioms.py"))["parse_output"]
    names = []
    commands = [f"import {name}" for name in MODULES]
    for name in MODULES:
        declarations = AUDIT_COMMAND.findall((HERE.parent / f"{name}.lean").read_text())
        if not declarations:
            raise ValueError(f"No named axiom checks in {name}")
        names.extend(declarations)
        commands.extend(f"#print axioms {declaration}" for declaration in declarations)
    (directory / "MarkedRowAxioms.lean").write_text("\n".join(commands) + "\n")
    result = subprocess.run(
        ["lake", "env", "lean", "-j1", "MarkedRowAxioms.lean"],
        cwd=directory, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    reports = parse_output(result.stdout, names)
    (directory / "axioms.json").write_text(json.dumps(reports, indent=2) + "\n")
    print(f"Verified {len(reports)} declaration-specific axiom reports.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("stage", "audit"))
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    action = stage if args.action == "stage" else audit
    action(args.directory.resolve())
