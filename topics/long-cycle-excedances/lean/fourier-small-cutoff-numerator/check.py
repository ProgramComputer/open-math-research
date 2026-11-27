#!/usr/bin/env python3
"""Audit the actual two-band small-cutoff Fourier numerator on the common pin."""

import argparse
from pathlib import Path
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
HIGH = runpy.run_path(str(HERE.parent / "fourier-high-height" / "check.py"))
LOW = runpy.run_path(str(HERE.parent / "fourier-numerator" / "check.py"))
MODULES = (
    "SmallCutoffPoisson", "SmallCutoffFrequency", "HighBandNumerator",
    "HighBandConstants", "SmallCutoffHighPoints", "SmallCutoffHighBands", "LowBandRadial",
    "LowBandContraction", "LowBandLiteral", "SmallCutoffLowPoints", "RepositorySmallCutoffNumerator",
)


def compile_small_cutoff_numerator(project):
    """Check these modules in an authenticated project with the original prerequisites."""
    failed = set()
    count = 0
    for module in MODULES:
        source = HERE / (module + ".lean")
        imports = {line.split()[1] for line in source.read_text().splitlines()
                   if line.startswith("import ")}
        if imports & failed:
            print(f"Skip {module} because its imports failed: {sorted(imports & failed)}", flush=True)
            failed.add(module)
            continue
        namespace = HIGH["ORIGINAL"] if module == "RepositorySmallCutoffNumerator" else HIGH["GENERIC"]
        try:
            count += HIGH["check_module"](project, source, namespace)
        except (subprocess.CalledProcessError, ValueError):
            failed.add(module)
    if failed:
        raise RuntimeError(f"Incomplete small-cutoff numerator checks: {sorted(failed)}")
    print(f"PASS: {count} small-cutoff numerator declarations audited", flush=True)
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--retained-imports", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    imports = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    HIGH["STABLE"]["main"](project, True, imports, continuation=True)
    LOW["compile_numerator"](project)
    for source, namespace in HIGH["MODULES"]:
        HIGH["check_module"](project, source, namespace)
    compile_small_cutoff_numerator(project)


if __name__ == "__main__":
    main()
