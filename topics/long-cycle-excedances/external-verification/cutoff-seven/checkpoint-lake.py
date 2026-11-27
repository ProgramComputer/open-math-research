#!/usr/bin/env python3
"""Retain the already compiled supplier before building the audit comparator."""
import hashlib
import os
from pathlib import Path
import subprocess
import sys


lake = os.environ["SUPPLIER_LAKE"]
checkpoint = Path(os.environ["SUPPLIER_CHECKPOINT"])
comparator = "+" + os.environ["SUPPLIER_COMPARATOR"]
args = sys.argv[1:]
if args[:2] == ["--wfail", "build"] and comparator in args[2:] and not checkpoint.exists():
    supplier_targets = [target for target in args[2:] if target != comparator]
    if supplier_targets:
        subprocess.run([lake, *args[:2], *supplier_targets], check=True)
    # The supplier's verifier uses a temporary build checkout. Keep its
    # locked source configuration and project objects before that cleanup.
    lean_root = Path(".lake/build/lib/lean")
    sources = []
    for folder, directories, files in os.walk("."):
        directories[:] = [d for d in directories if d != ".lake"]
        sources.extend(Path(folder) / filename for filename in files if filename.endswith(".lean"))
    sources.sort()
    source_manifest = Path("cutoff-seven-compiler-inputs.sha256")
    source_manifest.write_text("".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path}\n" for path in sources
    ))
    partial = checkpoint.with_name(checkpoint.name + ".part")
    subprocess.run(
        ["tar", "--zstd", "-cf", str(partial), str(lean_root), "lakefile.toml",
         "lake-manifest.json", "lean-toolchain", str(source_manifest), *map(str, sources)],
        check=True,
    )
    partial.replace(checkpoint)
    print(f"Supplier checkpoint ready: {checkpoint}", flush=True)

os.execv(lake, [lake, *args])
