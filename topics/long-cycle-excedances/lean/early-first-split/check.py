#!/usr/bin/env python3
"""Check all 47 finite certificates on the authenticated production pin."""
from hashlib import sha256
from pathlib import Path
import runpy
import sys

from emit import CUTOFFS, emit_cases

HERE = Path(__file__).resolve().parent
EARLY = runpy.run_path(str(HERE.parent / "early-sector/check.py"))
BUILD = EARLY["STABLE"]["build_local"]
DATA_SHA = "3dd81b6b8f6ca7c613ba5fdd47937189588f78b268fbda32ed24bf7102a59040"


def main(project, retained_imports):
    digest = sha256((HERE / "first-split.jsonl").read_bytes()).hexdigest()
    if digest != DATA_SHA:
        raise ValueError(f"Unexpected first-split data SHA-256: {digest}")
    print(f"47 finite certificates, data-sha256={digest}", flush=True)
    EARLY["main"](project, retained_imports)

    generated = project / "first-split-inputs"
    generated.mkdir()
    emit_cases(generated)
    for k in CUTOFFS:
        module = f"FirstSplitCase{k}"
        BUILD(project, generated / f"{module}.lean", module, (f"{module}.strict",))
    module = "FirstSplitFinite"
    BUILD(project, generated / f"{module}.lean", module, ("finite_first_split_strict",))
    module = "RepositoryThroughFirstSplit"
    BUILD(project, HERE / f"{module}.lean", module,
          ("original_first_split_all_cutoffs", "original_through_first_split"))
    print("PASS: 47 first-split certificates and the complete literal first sector", flush=True)


if __name__ == "__main__":
    project = Path(sys.argv[1]).resolve()
    archive = Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None
    main(project, archive)
