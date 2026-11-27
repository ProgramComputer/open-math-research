"""Build and replay the original wide-aspect interlacing theorem."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
BASE = runpy.run_path(str(LEAN / "angular-interlacing/check.py"))
NEW = {"FourierPhaseEntrance", "RepositoryWidePhaseCells", "RepositoryWideInterlacing"}
ROOT = "RepositoryWideInterlacing"
SUPPLIED = "RepositoryFourierPairedRows"
FINAL = "RepositoryQuotientAudit.original_wide_aspect_interlacing"


def plan():
    directories = (*BASE["SOURCE_DIRS"], HERE, LEAN / "fourier-odd-moments", LEAN / "fourier-circle",
                   LEAN / "fourier-stable")
    ordered, frozen = BASE["plan"](ROOT, NEW, directories, {SUPPLIED})
    if "CutoffFormalExp" in ordered:
        raise ValueError("The prepared Fourier project uses the vertical cutoffExp convention")
    return ordered, frozen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path, help="a fresh check directory")
    parser.add_argument("--retained-imports", type=Path, help="authenticated common-pin objects")
    parser.add_argument("--plan", action="store_true", help="list the additional import closure")
    args = parser.parse_args()
    ordered, frozen = plan()
    if args.plan:
        for module, (source, data) in ordered.items():
            print(f"{module} {source.relative_to(BASE['REPO'])} {sha256(data).hexdigest()}")
        print("Frozen imports:", " ".join(sorted(frozen)))
        return
    if args.project is None:
        parser.error("a fresh project directory is required unless --plan is given")
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(LEAN / "fourier-centered/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    supplier = LEAN / "fourier-centered" / f"{SUPPLIED}.lean"
    staged = project / supplier.name
    compiled = project / ".lake/build/lib/lean" / f"{SUPPLIED}.olean"
    if not compiled.is_file() or staged.read_bytes() != supplier.read_bytes():
        raise ValueError(f"Prepared project lacks the exact centered-row supplier {SUPPLIED}")
    BASE["compile_closure"](project, ordered, frozen, new=NEW, final=FINAL,
                            rename_vertical=False, reuse=True, strict=True)


if __name__ == "__main__":
    main()
