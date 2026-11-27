#!/usr/bin/env python3
"""Rebuild the original-row adapter against the authenticated Zuo release."""
from hashlib import sha256
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
STABLE = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))
COMMON = STABLE["COMMON"]


def main(project, retained_imports):
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    run(project, "lake", "exe", "cache", "get")
    mathlib = run(project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD", capture=True).strip()
    if mathlib != COMMON["MATHLIB"]:
        raise ValueError(f"Unexpected mathlib: {mathlib}")
    print(f"mathlib {mathlib}", flush=True)

    file = Path("LongCycleBounds/InitialRows.lean")
    source = project / file
    print(f"Upstream LongCycleBounds.InitialRows input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    if retained_imports is None:
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.InitialRows")
    else:
        digest = sha256(retained_imports.read_bytes()).hexdigest()
        if digest != COMMON["IMPORT_SHA"]:
            raise ValueError(f"Unexpected retained object archive: {digest}")
        run(project, "tar", "--zstd", "-xf", str(retained_imports))
        print(f"Reused verified 65-module archive sha256={digest}", flush=True)
        output = (project / ".lake/build/lib/lean" / file).with_suffix(".olean")
        run(project, "lake", "env", "lean", "-DwarningAsError=true", "-o", str(output), str(source))
    run(project, "lake", "env", "leanchecker", "--verbose", "LongCycleBounds.InitialRows")
    print("kernel_replay_exit=0 LongCycleBounds.InitialRows", flush=True)
    module = "RepositoryEarlySector"
    STABLE["build_local"](project, HERE / f"{module}.lean", module,
                          ("original_before_first_split", "original_at_first_split"))


if __name__ == "__main__":
    project = Path(sys.argv[1]).resolve()
    archive = Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None
    main(project, archive)
