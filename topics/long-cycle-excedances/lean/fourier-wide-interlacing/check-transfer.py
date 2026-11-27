"""Check the original phase and root transfer with the centered estimate as a premise."""
import argparse
from hashlib import sha256
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
BASE = runpy.run_path(str(LEAN / "angular-interlacing/check.py"))
ROOT = "RepositoryWideRootTransfer"
NEW = {ROOT, "RepositoryWidePhaseTransfer", "FourierPhaseEntrance"}
FINAL = "RepositoryQuotientAudit.original_wide_aspect_interlacing_of_centered"


def plan():
    directories = (*BASE["SOURCE_DIRS"], HERE, LEAN / "fourier-odd-moments", LEAN / "fourier-circle")
    return BASE["plan"](ROOT, NEW, directories)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    parser.add_argument("--plan", action="store_true")
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
    archive = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    common = runpy.run_path(str(LEAN / "common-pin/check.py"))
    BASE["start"](project, archive, common)
    BASE["compile_closure"](project, ordered, frozen, new=NEW, final=FINAL, strict=True)


if __name__ == "__main__":
    main()
