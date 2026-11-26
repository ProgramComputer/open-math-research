"""Stage a clean build of the published Lean sources and their stable-version ports."""
import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = "312293aa850010e9d9509d6850a482b9c7b7966f"
MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
GROUPS = {
    "catalan": ["CatalanStrictPeaksAllInterlacing"],
    "prism": ["PrismDimensions", "PrismFamilyInterlacing"],
    "balanced": ["BalancedNoFullRowCounting", "BalancedTorusComponents",
                 "OpenMathResearch.DiskUniqueness", "BalancedThreeColumnSigns"],
    "ordered": ["OrderedThresholdTwoSigns", "OrderedThresholdTwoPhase",
                "OrderedThresholdThreeSigns", "OrderedGlobalAngular", "OrderedThresholdFourSigns"],
    "eulerian": ["EulerianRootSpacing", "EulerianCluster", "OpenMathResearch.DiskUniqueness"],
    "ribbon": ["Ribbon", "RibbonExamples"],
}
NEW_IMPORTS = {
    "Mathlib.Combinatorics.Enumerative.Catalan": "Mathlib.Combinatorics.Enumerative.Catalan.Basic",
    "Mathlib.Data.Real.Pi.Bounds": "Mathlib.Analysis.Real.Pi.Bounds",
}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=HERE.parents[2], text=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("group", choices=GROUPS)
    parser.add_argument("dest", type=Path)
    args = parser.parse_args()
    dest = args.dest.resolve()
    dest.mkdir(parents=True, exist_ok=True)
    files = {}
    for path in git("ls-tree", "-r", "--name-only", BASE, "topics", "shared/lean/OpenMathResearch").splitlines():
        if not path.endswith(".lean") or "/lean/" not in path:
            continue
        name = Path(path).stem
        if path.startswith("shared/"):
            name = "OpenMathResearch." + name
        if name in files:
            # Standalone axiom-printing files with repeated names are not libraries.
            continue
        files[name] = path
    roots = GROUPS[args.group]
    pending = list(roots)
    modules = {}
    mathlib = set()
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        source = git("show", BASE + ":" + files[name])
        for old,new in NEW_IMPORTS.items():
            source = source.replace("import "+old+"\n", "import "+new+"\n")
        relative = Path(*name.split(".")).with_suffix(".lean")
        path = dest / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        patch = HERE / "ports" / (name + ".patch")
        if patch.exists():
            subprocess.run(["patch", "--fuzz=0", "-s", str(path), str(patch)], check=True)
            source = path.read_text()
        modules[name] = files[name]
        for mod in re.findall(r"(?m)^(?:public )?import ([\w.]+)", source):
            if mod in files:
                pending.append(mod)
            elif mod.startswith("Mathlib."):
                mathlib.add(mod)
    config = ['name = "published_audit"', 'version = "0.1.0"', '',
              '[[require]]', 'name = "mathlib"', 'scope = "leanprover-community"',
              'git = "https://github.com/leanprover-community/mathlib4.git"', f'rev = "{MATHLIB}"']
    for mod in sorted(modules):
        config.extend(['', '[[lean_lib]]', f'name = "{mod}"'])
    (dest / "lakefile.toml").write_text("\n".join(config)+"\n")
    for filename in ("lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(HERE / filename, dest / filename)
    (dest / "targets.txt").write_text("\n".join(roots)+"\n")
    (dest / "cache-imports.txt").write_text("\n".join(sorted(mathlib))+"\n")
    (dest / "sources.json").write_text(json.dumps(modules, indent=2)+"\n")
    print(f"{args.group}: {len(modules)} published source modules, {len(mathlib)} direct mathlib imports")


if __name__ == "__main__":
    main()
