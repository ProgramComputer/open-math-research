"""Stage a clean build of the published Lean sources and their stable-version ports."""
import argparse
import hashlib
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


def split_certificate_rows(source):
    """Keep the published literals in order, elaborating each array row separately."""
    for name, row_type in (("prefixCoefficients", "List ℕ"), ("prefixBoxes", "Boxes")):
        heading = f"def {name} : Array {row_type if row_type == 'Boxes' else '(List ℕ)'} := #["
        start = source.index(heading)
        end = source.index("\n]", start)
        literal = source[start + len(heading):end]
        # The generator indents the start of each row by two spaces and the
        # continuation of each tuple list by four. Retain the literal text.
        rows = [r.strip() for r in re.split(r"(?m)(?=^  #?\[)", literal) if r.strip()]
        if len(rows) != 151 or any(not row.endswith("],") for row in rows):
            raise ValueError(f"invalid published certificate array {name}")
        definitions = []
        names = []
        for i, row in enumerate(rows):
            row_name = f"{name}Row{i}"
            definitions.append(f"private def {row_name} : {row_type} := {row[:-1]}")
            names.append(row_name)
        replacement = "\n\n".join(definitions) + "\n\n" + heading + ", ".join(names) + "]"
        source = source[:start] + replacement + source[end + 2:]
    return source


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
    additional = {}
    if args.group in ("catalan", "prism"):
        topic = "catalan-word-peaks" if args.group == "catalan" else "prism-splitting"
        for path in (HERE.parents[2]/"topics"/topic/"lean"/"publication").glob("Audit*.lean"):
            additional[path.stem] = path
        additional["AuditReferenceSpecs"] = HERE/"reference"/"AuditReferenceSpecs.lean"
        files.update({k: str(v.relative_to(HERE.parents[2])) for k,v in additional.items()})
    roots = GROUPS[args.group]+sorted(additional)
    pending = list(roots)
    modules = {}
    mathlib = set()
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        source = additional[name].read_text() if name in additional else git("show", BASE + ":" + files[name])
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
        if args.group == "catalan":
            if name == "CatalanStrictPeaksIntervalData":
                source = split_certificate_rows(source)
            # Mathlib 4.36 makes the coefficient ring implicit in these maps.
            source = re.sub(r"PowerSeries\.(coeff|C|constantCoeff) (ℝ|ℂ|P|R|S)(?![\w'])",
                            r"PowerSeries.\1 («R» := \2)", source)
            source = source.replace("eval_finset_sum", "eval_finsetSum")
            source = re.sub(r"(Nat\.strong_induction_on with\n\s*\| )h ", r"\1ind ", source)
            path.write_text(source)
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
    sources = {module: {"published_path": original, "staged_sha256":
                hashlib.sha256((dest / Path(*module.split(".")).with_suffix(".lean")).read_bytes()).hexdigest()}
               for module, original in modules.items()}
    (dest / "sources.json").write_text(json.dumps(sources, indent=2)+"\n")
    print(f"{args.group}: {len(modules)} published source modules, {len(mathlib)} direct mathlib imports")


if __name__ == "__main__":
    main()
