#!/usr/bin/env python3
"""Build only the import closure of the literal bounded-aspect interlacing theorem."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
import runpy
import subprocess


HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
TOPIC = LEAN.parent
REPO = TOPIC.parents[1]
SOURCE_DIRS = (
    HERE, LEAN, REPO / "shared/lean", TOPIC / "phase-cells", TOPIC / "color-acceptance",
    TOPIC / "color-load-bounds", LEAN / "common-pin", LEAN / "pinned-quotient",
    LEAN / "paired-profile", LEAN / "sine-comparison", LEAN / "probability-bands",
    LEAN / "front-middle-join", LEAN / "all-aspect-exterior", LEAN / "front-envelope-sums",
    LEAN / "sparse-sector", LEAN / "uniform-log-tilt", LEAN / "vertical-tilt", LEAN / "middle-residues",
)
ROOT = "RepositoryBoundedInterlacing"
NEW = {
    ROOT, "IntegerMiddleSeam", "DeterminantCellSigns", "AngularRootSelection",
    "BoundedAngularWitnesses", "BoundedAspectSlabs",
}
FINAL = "RepositoryQuotientAudit.original_bounded_aspect_interlacing"
FROZEN = {"LongCycleBounds", "LongCycleFinite", "LongCycles", "Cluster"}
EXTERNAL = {"Mathlib", "Lean", "Std", "Init", "Batteries"}
PATCH_PORTS = {"OpenMathResearch.AlternatingSignRoots", "OpenMathResearch.OrientedNegativeInterlace"}
TEXT_PORTS = {
    "LongCycleRunColors": (b"Polynomial.finset_sum_coeff", b"Polynomial.finsetSum_coeff"),
    "LongCyclePrefixTail": (
        b"add_le_add_left hlo _, add_le_add_left hhi _",
        b"add_le_add (le_refl (c 0)) hlo, add_le_add (le_refl (c 0)) hhi",
    ),
}
IMPORT_LINE = re.compile(r"^(?:(?:public|meta|private)[ \t]+)*import[ \t]+([^\n]+)", re.MULTILINE)
AXIOM_COMMAND = re.compile(r"^#print axioms ([\w.]+)$", re.MULTILINE)
NAMESPACE = re.compile(r"^namespace ([\w.]+)$", re.MULTILINE)


def module_filename(module, suffix=".lean"):
    if not re.fullmatch(r"\w+(?:\.\w+)*", module):
        raise ValueError(f"Invalid module name: {module!r}")
    return module.replace(".", "/") + suffix


def imports(data):
    return [name for line in IMPORT_LINE.findall(data.decode()) for name in line.partition("--")[0].split()]


def read_source(path):
    if path.is_file():
        return path.read_bytes()
    # Allow dependency planning in a sparse linked checkout.
    relative = path.relative_to(REPO)
    return subprocess.check_output(["git", "show", f":{relative}"], cwd=REPO)


def plan():
    tracked = {
        REPO / Path(path) for path in subprocess.check_output(
            ["git", "ls-files", "-z", "--", "*.lean"], cwd=REPO
        ).decode().split("\0") if path
    }
    ordered = {}
    frozen = set()
    visiting = set()

    def visit(module):
        prefix = module.split(".")[0]
        if prefix in FROZEN:
            frozen.add(module)
            return
        if prefix in EXTERNAL or module in ordered:
            return
        if module in visiting:
            raise ValueError(f"Cyclic repository import at {module}")
        filename = module_filename(module)
        matches = [directory / filename for directory in SOURCE_DIRS if directory / filename in tracked]
        if len(matches) != 1:
            raise ValueError(f"Expected one source for {module}, found {matches}")
        path, = matches
        data = read_source(path)
        visiting.add(module)
        for dependency in imports(data):
            visit(dependency)
        visiting.remove(module)
        ordered[module] = (path, data)

    visit(ROOT)
    if NEW - ordered.keys() or len({path for path, _ in ordered.values()}) != len(ordered):
        raise ValueError("Missing proof module or a source assigned to more than one module")
    return ordered, frozen


def stage(project, module, data):
    target = project / module_filename(module)
    target.parent.mkdir(parents=True, exist_ok=True)
    if module in TEXT_PORTS:
        old, new = TEXT_PORTS[module]
        if old not in data:
            raise ValueError(f"Stale common-pin port for {module}")
        target.write_bytes(data.replace(old, new))
    else:
        target.write_bytes(data)
    if module in PATCH_PORTS:
        patch = REPO / "shared/lean/publication/ports" / (module + ".patch")
        edits = read_source(patch)
        print(f"Port {module} patch-sha256={sha256(edits).hexdigest()}", flush=True)
        subprocess.run(["patch", "--batch", str(target)], input=edits, check=True)
    if imports(target.read_bytes()) != imports(data):
        raise ValueError(f"Port changes the planned imports of {module}")
    return target


def start(project, archive, common):
    project.mkdir(parents=True)
    common["prepare"](project)
    run = common["run"]
    version = run(project, "lean", "--version", capture=True).strip()
    if common["COMPILER"] not in version:
        raise ValueError(f"Unexpected compiler {version}")
    print(version, flush=True)
    run(project, "lake", "exe", "cache", "get")
    mathlib = run(project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD", capture=True).strip()
    if mathlib != common["MATHLIB"]:
        raise ValueError(f"Unexpected mathlib {mathlib}")
    print(f"mathlib {mathlib}", flush=True)
    if archive is None:
        run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient")
    else:
        digest = sha256(archive.read_bytes()).hexdigest()
        if digest != common["IMPORT_SHA"]:
            raise ValueError(f"Unexpected import archive {digest}")
        run(project, "tar", "--zstd", "-xf", str(archive))
        print(f"Reused verified common-pin archive sha256={digest}", flush=True)


def production(project, archive, ordered, frozen):
    common = runpy.run_path(str(LEAN / "common-pin/check.py"))
    paired = runpy.run_path(str(LEAN / "paired-profile/check.py"))
    start(project, archive, common)
    objects = project / ".lake/build/lib/lean"
    run = common["run"]
    upstream_order = tuple("LongCycleBounds." + m for m in (*common["LOGISTIC_IMPORTS"], "UniversalRecurrence"))

    def upstream(module):
        out = objects / module_filename(module, ".olean")
        if out.is_file():
            return
        source = project / module_filename(module)
        data = source.read_bytes()
        for dependency in imports(data):
            if dependency.split(".")[0] in FROZEN:
                upstream(dependency)
        print(f"Compile frozen {module} input-sha256={sha256(data).hexdigest()}", flush=True)
        out.parent.mkdir(parents=True, exist_ok=True)
        run(project, "lake", "env", "lean", "-o", str(out), str(source))

    for module in (*[m for m in upstream_order if m in frozen], *sorted(frozen - set(upstream_order))):
        upstream(module)
    failed = set()
    seen = {}
    expected = set()
    for module, (original, data) in ordered.items():
        if blocked := failed.intersection(imports(data)):
            failed.add(module)
            print(f"Skip {module} after failed imports {sorted(blocked)}", flush=True)
            continue
        source = stage(project, module, data)
        out = objects / module_filename(module, ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        print(f"Compile {module} path={original.relative_to(REPO)} source-sha256={sha256(data).hexdigest()} "
              f"input-sha256={sha256(source.read_bytes()).hexdigest()}", flush=True)
        result = subprocess.run(["lake", "env", "lean", "-o", str(out), str(source)],
                                cwd=project, capture_output=True, text=True)
        print(result.stdout, end="", flush=True)
        print(result.stderr, end="", flush=True)
        if result.returncode:
            failed.add(module)
        if module in NEW:
            namespace, = NAMESPACE.findall(data.decode())
            expected.update(f"{namespace}.{name}" for name in AXIOM_COMMAND.findall(data.decode()))
            seen.update({name: {a.strip() for a in axioms.split(",") if a.strip()}
                         for name, axioms in paired["AXIOM_REPORT"].findall(result.stdout)})
    if failed:
        raise RuntimeError(f"Module compilation failed or was blocked: {sorted(failed)}")
    if FINAL not in expected:
        raise ValueError(f"Missing axiom command for {FINAL}")
    for name in sorted(expected):
        if name not in seen or seen[name] - common["ALLOWED"]:
            raise ValueError(f"Missing declaration or unexpected axioms for {name}: {seen.get(name)}")
    for module in ordered:
        if module in NEW:
            run(project, "lake", "env", "leanchecker", "--verbose", module)
            print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(ordered)} repository modules compiled, {len(NEW)} replayed, "
          f"{len(expected)} original-proof declarations audited", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path)
    parser.add_argument("--import-archive", type=Path)
    parser.add_argument("--plan", action="store_true")
    opts = parser.parse_args()
    ordered, frozen = plan()
    if opts.plan:
        for module, (path, data) in ordered.items():
            print(f"{module} {path.relative_to(REPO)} {sha256(data).hexdigest()}")
        print("Frozen imports:", " ".join(sorted(frozen)))
    elif opts.project:
        production(opts.project.resolve(), opts.import_archive.resolve() if opts.import_archive else None, ordered, frozen)
    else:
        parser.error("a fresh project directory is required unless --plan is given")


if __name__ == "__main__":
    main()
