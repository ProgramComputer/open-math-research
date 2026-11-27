#!/usr/bin/env python3
"""Build and audit the original-row adapter with the frozen upstream project."""

import re
import shutil
import subprocess
import sys
from hashlib import sha256
from io import BytesIO
from pathlib import Path
from zipfile import ZipFile


TAG = "v1.2.0"
COMMIT = "46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554"
OUTER = "37ec19f48e46eddcaa7a59efb6026b006a61b2a8f753835c585af950bf245527"
INNER = "605cd388a15d43d5c557605007b9f9e12e1db9cebd11ca80cb9abc33d67004c1"
MANIFEST = "baa9bca94f285968d119941f92d946a2b4be4a212e342e8d599f401f42f90ac6"
HERE = Path(__file__).resolve().parent


def check_digest(data, expected):
    if sha256(data).hexdigest() != expected:
        raise ValueError("frozen input digest mismatch")


def fixture_evaluations():
    source = (HERE.parent / "LongCyclePrefixTail.lean").read_text()
    for n in (14, 15):
        declaration = source.split(f"private def quotient{n}Coeff : ℕ → ℕ", 1)[1]
        table = declaration.split("| _ => 0", 1)[0]
        values = [(int(j), int(value)) for j, value in re.findall(r"\| (\d+) => (\d+)", table)]
        if [j for j, _ in values] != list(range(n - 1)):
            raise ValueError(f"unexpected coefficient fixture for size {n}")
        ordered = ", ".join(str(value) for _, value in values)
        yield f"""
#eval show IO Unit from do
  let expected : List ℚ := [{ordered}]
  let actual := (List.range {n - 1}).map
    (RepositoryQuotientAudit.cycleQuotientCoeff RepositoryQuotientAudit.exactEulerianCoeff {n} 7)
  unless actual == expected do
    throw (IO.userError s!"cutoff seven, size {n}: {{actual}}")
  IO.println "cutoff seven, size {n}: all {n - 1} fixture coefficients match"
"""


def main(directory):
    directory.mkdir(parents=True)
    checkout = directory / "release"
    subprocess.run(
        ["git", "clone", "--depth", "1", "--branch", TAG,
         "https://github.com/AlexZander-666/long-cycle-excedance-interlacing.git", checkout],
        check=True,
    )
    observed = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if observed != COMMIT:
        raise ValueError("unexpected upstream commit")
    outer = (checkout / "cutoff-six/formal/cutoff-six-all-accepted.zip").read_bytes()
    check_digest(outer, OUTER)
    with ZipFile(BytesIO(outer)) as archive:
        inner = archive.read("cutoff-six-all-source.zip")
    check_digest(inner, INNER)
    project = directory / "formal"
    with ZipFile(BytesIO(inner)) as archive:
        if any(Path(name).is_absolute() or ".." in Path(name).parts for name in archive.namelist()):
            raise ValueError("invalid path in frozen archive")
        archive.extractall(project)
    subprocess.run(["sha256sum", "--quiet", "-c", "SHA256SUMS"], cwd=project, check=True)
    check_digest((project / "lake-manifest.json").read_bytes(), MANIFEST)
    if (project / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        raise ValueError("unexpected toolchain pin")

    # Modules are identical to the repository source, except for the generated
    # runtime assertions against the existing coefficient fixture.
    filename = "RepositoryQuotientAdapter.lean"
    shutil.copy2(HERE / filename, project / filename)
    with (project / filename).open("a") as module:
        module.writelines(fixture_evaluations())
    subprocess.run(
        [sys.executable, "-Bu", "verify_lean.py", ".", "RepositoryQuotientAdapter", "--serial"],
        cwd=project, check=True,
    )


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
