#!/usr/bin/env python3
"""Check the original Fourier numerator contraction at cutoffs eight and nine."""
import argparse
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE.parent / "fourier-small-cutoff-numerator" / "check.py"))
HIGH = BASE["HIGH"]
LOW = BASE["LOW"]


def compile_eight_nine_numerator(project):
    modules = [(name, HIGH["GENERIC"]) for name in ("EightNineConstants", "EightNineHigh")]
    modules.append(("RepositoryEightNineNumerator", HIGH["ORIGINAL"]))
    count = sum(HIGH["check_module"](project, HERE / (module + ".lean"), namespace)
                for module, namespace in modules)
    print(f"PASS: {count} cutoff-eight and cutoff-nine declarations audited", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="an empty output directory")
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    HIGH["STABLE"]["main"](project, True, retained, continuation=True)
    LOW["compile_numerator"](project)
    for source, namespace in HIGH["MODULES"]:
        HIGH["check_module"](project, source, namespace)
    BASE["compile_small_cutoff_numerator"](project)
    compile_eight_nine_numerator(project)


if __name__ == "__main__":
    main()
