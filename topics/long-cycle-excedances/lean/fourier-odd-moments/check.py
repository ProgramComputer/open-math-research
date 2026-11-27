"""Check the discrete signed pole moments on the common pin."""
import argparse
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
REAL_AXIS = runpy.run_path(str(HERE.parent / "fourier-stable/check-real-axis.py"))
COMMON = REAL_AXIS["COMMON"]
DEFINITIONS = HERE.parent / "fourier-circle/NumeratorLogDefinitions.lean"
MANIFEST = (
    (DEFINITIONS, ()),
    (HERE / "DiscretePoleEnvelope.lean", (
        "discrete_pole_decay", "discrete_pole_weighted_prefix", "discrete_pole_unweighted_prefix",
    )),
    (HERE / "LiteralDiscretePoleMoments.lean", (
        "literal_discrete_pole_decay", "literal_discrete_pole_moments",
        "literal_discrete_pole_moments_of_size", "literal_discrete_pole_norm_moments",
    )),
)


def compile_moments(project):
    (project / ".lake/build/lib/lean").mkdir(parents=True, exist_ok=True)
    build = REAL_AXIS["build_local"]
    for source, declarations in MANIFEST:
        build(project, source, source.stem, declarations)
    print(f"PASS: {sum(len(names) for _, names in MANIFEST)} moment declaration audits", flush=True)


def main(project):
    project.mkdir(parents=True)
    COMMON["prepare"](project)
    run = COMMON["run"]
    compiler = run(project, "lean", "--version", capture=True).strip()
    if COMMON["COMPILER"] not in compiler:
        raise ValueError(f"Unexpected compiler: {compiler}")
    print(compiler, flush=True)
    imports = sorted({
        line.removeprefix("import ")
        for src, _ in MANIFEST
        for line in src.read_text().splitlines()
        if line.startswith("import Mathlib.")
    })
    run(project, "lake", "exe", "cache", "get", *imports)
    packages = json.loads((project / "lake-manifest.json").read_text())["packages"]
    for entry in packages:
        package = entry["name"]
        revision = run(project, "git", "-C", f".lake/packages/{package}",
                       "rev-parse", "HEAD", capture=True).strip()
        if revision != entry["rev"]:
            raise ValueError(f"Wrong revision for {package}: {revision}")
        print(f"{package} {revision}", flush=True)
    compile_moments(project)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="new directory for the check")
    main(parser.parse_args().project.resolve())
