"""Check the finite conjugate pairing on the exact original pole definitions."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))
MODULE = "EnclosedPolePairing"
THEOREMS = {
    "positive_enclosed_pole_index", "enclosed_positive_half",
    "enclosed_minor_indices_eq_range", "enclosed_poles_conjugate_pairing",
    "enclosed_poles_real_half",
}
AXIOM = re.compile(r"^'RepositoryQuotientAudit\.(\w+)' depends on axioms:\s*\[([^\]]*)\]", re.M)


def compile_enclosed_pairing(project):
    """Build the finite pairing in a project with the original pole modules."""
    source = project / f"{MODULE}.lean"
    source.write_bytes((HERE / source.name).read_bytes())
    output = project / ".lake/build/lib/lean" / f"{MODULE}.olean"
    print(f"Compile {MODULE} input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "-o", str(output), str(source)],
        cwd=project, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    reports = AXIOM.findall(result.stdout)
    if len(reports) != len(THEOREMS) or set(dict(reports)) != THEOREMS:
        raise ValueError("Missing or duplicate finite-pairing axiom audits")
    for theorem, names in reports:
        axioms = {name.strip() for name in names.split(",") if name.strip()}
        if not axioms <= BASE["COMMON"]["ALLOWED"]:
            raise ValueError(f"Unexpected axioms for {theorem}: {sorted(axioms)}")
    BASE["COMMON"]["run"](project, "lake", "env", "leanchecker", "--verbose", MODULE)
    print(f"kernel_replay_exit=0 {MODULE}", flush=True)
    print(f"PASS: {len(THEOREMS)} finite-pairing declaration audits", flush=True)


def main(project, retained_imports):
    BASE["main"](project, original_log=True, retained_imports=retained_imports, continuation=True)
    moments = runpy.run_path(str(HERE.parent / "fourier-odd-moments/check.py"))
    moments["compile_moments"](project)
    compile_enclosed_pairing(project)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the check")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin import archive")
    args = parser.parse_args()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    main(args.project.resolve(), retained)
