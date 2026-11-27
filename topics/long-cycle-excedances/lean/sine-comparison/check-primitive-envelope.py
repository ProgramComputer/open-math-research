#!/usr/bin/env python3
"""Build the marked-bin bridge with the exact research dependency sources."""

import argparse
import importlib.util
import json
import re
import shutil
import subprocess
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOTS = (
    "LinearSlabs",
    "LiteralLinearTable",
    "BivariateBin",
    "DiscreteOddTail",
    "DyadicStarCertificate",
    "LiteralBin",
    "LiteralBinSupport",
    "LiteralBinTruncation",
    "PrimitiveBinAssembly",
    "PrimitiveBinMass",
    "PrimitiveCheckerMass",
    "PrimitiveFirstBlock",
    "PrimitiveLinearEnvelope",
    "PrimitiveNumeratorInputs",
    "PrimitivePoleKernel",
    "SignedStarEnvelope",
)
NAMESPACE = "OpenMathResearch.LongCycleExcedances."
AUDITED = (
    "linearHead_upper",
    "linearTail_upper",
    "linearTable_rounding",
    "linearSlabInputs",
    "literal_slab_linear_envelope_of_spec",
    "original_slab_linear_envelope",
    "markedMultiple_eq",
    "marked_bin_bounds",
    "coeff_markDegreeBin",
    "coeff_le_forgetDegree",
    "odd_step_le_tail_difference",
    "odd_tail_finite_prefix",
    "finite_star_dyadic_bound",
    "literalPrimitive_norm_formula",
    "coeff_forgetDegree_markDegreeBin",
    "literal_occupied_bin_integer_bound",
    "degreeBin_bounds",
    "literal_multiple_support",
    "literal_multiple_truncation",
    "checker_shape_tail_guard",
    "literal_checker_linear_envelope",
    "degreeBin_iff",
    "primitive_atom_mass",
    "primitive_factorial_bin_mass",
    "primitive_all_checker_bin_mass",
    "checker_degree_floor_le",
    "primitive_first_checker_bin_mass",
    "primitive_first_block_subset_mass",
    "primitive_bin_kernel",
    "literal_bin_linear_bound",
    "original_checker_linear_envelope",
    "primitive_checker_numerator_inputs",
    "primitive_angular_bernoulli_kernel",
    "signed_star_envelope",
    "signed_mass_tail",
)
IMPORT = re.compile(r"^(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)
AXIOMS = re.compile(
    r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$",
    re.MULTILINE,
)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def plan():
    """Return a topological list of files and the external Mathlib roots."""
    topic = HERE.parent.parent
    directories = (HERE, HERE.parent / "paired-profile", HERE.parent / "probability-bands",
                   topic / "color-acceptance", topic / "color-load-bounds")
    expected = json.loads((HERE / "marked-bins-dependencies.json").read_text())
    inherited = {}
    ordered, seen, active, mathlib, upstream = [], set(), set(), set(), set()

    def visit(module):
        if module.startswith("Mathlib."):
            mathlib.add(module)
            return
        if module.startswith(("LongCycleBounds.", "LongCycles.", "Cluster.")):
            upstream.add(module)
            return
        if module in seen:
            return
        if module in active:
            raise ValueError(f"cyclic import: {module}")
        filename = module.replace(".", "/") + ".lean"
        candidates = [directory / filename for directory in directories if (directory / filename).is_file()]
        if len(candidates) != 1:
            raise ValueError(f"local import {module} must resolve exactly once, found {candidates}")
        source = candidates[0]
        if module not in ROOTS:
            actual = digest(source)
            inherited[module] = actual
            if expected.get(module) != actual:
                raise ValueError(f"unexpected inherited source for {module}: {actual}")
        active.add(module)
        for line in IMPORT.findall(source.read_text()):
            for dependency in line.partition("--")[0].split():
                visit(dependency)
        active.remove(module)
        seen.add(module)
        ordered.append((module, source))

    for module in ROOTS:
        visit(module)
    if inherited != expected:
        raise ValueError(f"dependency closure changed: {sorted(set(expected) - inherited.keys())}")
    return ordered, sorted(mathlib), sorted(upstream)


def stage(project, ordered):
    for module, source in ordered:
        target = project / (module.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if digest(source) != digest(target):
            raise ValueError(f"staging changed {module}")
        print(f"Stage {module} input-sha256={digest(target)}", flush=True)


def production(project, ordered, mathlib_roots, upstream, archive):
    spec = importlib.util.spec_from_file_location(
        "common_pin", HERE.parent / "common-pin" / "check.py"
    )
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    common.prepare(project)
    version = common.run(project, "lean", "--version", capture=True).strip()
    if common.COMPILER not in version:
        raise ValueError(f"unexpected compiler {version}")
    print(version, flush=True)
    common.run(project, "lake", "exe", "cache", "get", *(mathlib_roots if not upstream else []))
    mathlib = common.run(
        project, "git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD", capture=True
    ).strip()
    if mathlib != common.MATHLIB:
        raise ValueError(f"unexpected mathlib {mathlib}")
    print(f"mathlib {mathlib}", flush=True)

    if upstream:
        if archive is None:
            common.run(project, "lake", "--wfail", "build", "+LongCycleBounds.GeneralCycleQuotient")
        else:
            if digest(archive) != common.IMPORT_SHA:
                raise ValueError("unexpected retained object archive SHA-256")
            common.run(project, "tar", "--zstd", "-xf", str(archive.resolve()))
            print(f"Reused verified common-pin archive sha256={common.IMPORT_SHA}", flush=True)
        for module in upstream:
            source = module.replace(".", "/")
            if not (project / ".lake" / "build" / "lib" / "lean" / (source+".olean")).is_file():
                common.run(project, "lake", "--wfail", "build", "+"+module)
    stage(project, ordered)
    observed = {}
    failed = set()
    for module, _ in ordered:
        relative = module.replace(".", "/")
        source = project / (relative + ".lean")
        dependencies = {name for line in IMPORT.findall(source.read_text())
                        for name in line.partition("--")[0].split()}
        if blocked := failed & dependencies:
            print(f"Skip {module}: failed dependencies {sorted(blocked)}", flush=True)
            failed.add(module)
            continue
        output = project / ".lake" / "build" / "lib" / "lean" / (relative + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"Compile {module} input-sha256={digest(source)}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", "-o", str(output), str(source)], cwd=project,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="", flush=True)
        if result.returncode:
            failed.add(module)
            continue
        for name, axioms in AXIOMS.findall(result.stdout):
            observed[name] = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
    if failed:
        raise RuntimeError(f"Module compilation failed or was blocked: {sorted(failed)}")
    for name in AUDITED:
        fq = NAMESPACE + name
        if fq not in observed or observed[fq] - common.ALLOWED:
            raise ArithmeticError(f"Missing declaration or unexpected axioms for {fq}: {observed.get(fq)}")
    for module in ROOTS:
        common.run(project, "lake", "env", "leanchecker", "--verbose", module)
        print(f"kernel_replay_exit=0 {module}", flush=True)
    print(f"PASS: {len(AUDITED)} marked-bin declarations audited", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path, help="fresh scratch project directory")
    parser.add_argument("--import-archive", type=Path, help="authenticated upstream object archive")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--plan", action="store_true", help="authenticate and list inputs without building")
    mode.add_argument("--stage-only", action="store_true", help="copy and verify inputs without Lean")
    args = parser.parse_args()
    ordered, mathlib, upstream = plan()
    if args.plan:
        for module, file in ordered:
            print(f"{module} {digest(file)} {file.relative_to(HERE.parent.parent)}")
        print("Mathlib roots:", " ".join(mathlib))
        print("Upstream roots:", " ".join(upstream))
        return
    if args.project is None:
        parser.error("project is required unless --plan is used")
    project = args.project.resolve()
    project.mkdir(parents=True)
    if args.stage_only:
        stage(project, ordered)
    else:
        production(project, ordered, mathlib, upstream, args.import_archive)


if __name__ == "__main__":
    main()
