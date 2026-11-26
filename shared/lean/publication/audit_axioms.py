"""Require an explicit, standard-axiom-only report for every named declaration."""
import argparse
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALLOWED = {"Classical.choice", "propext", "Quot.sound"}


def parse_output(output, names):
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        reports[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        reports[name] = []
    if set(reports) != set(names):
        raise ValueError(f"missing or extra declarations: {sorted(set(reports) ^ set(names))}")
    for name, axioms in reports.items():
        if set(axioms) - ALLOWED:
            raise ValueError(f"{name} depends on unapproved axioms {axioms}")
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("topic")
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve()
    names = json.loads((HERE / "declarations.json").read_text())[args.topic]
    roots = (directory / "targets.txt").read_text().splitlines()
    commands = ["import " + target for target in roots]
    commands += ["\n#print axioms " + name for name in names]
    (directory / "PublishedAxioms.lean").write_text("\n".join(commands) + "\n")
    result = subprocess.run(["lake","env","lean","-j1","PublishedAxioms.lean"],
                            cwd=directory,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    reports = parse_output(result.stdout, names)
    (directory/"axioms.json").write_text(json.dumps(reports, indent=2)+"\n")
    print(f"Verified {len(reports)} declaration-specific axiom reports.")


if __name__ == "__main__":
    main()
