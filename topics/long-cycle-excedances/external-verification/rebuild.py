"""Rebuild Bowen Zuo's supplying release and compare its theorem with the unweighted claim."""
import argparse
from hashlib import sha256
from pathlib import Path
import json
import os
import subprocess
from zipfile import ZipFile

REPO = 'https://github.com/AlexZander-666/long-cycle-excedance-interlacing.git'
PINS = {
    4: ('v1.0.0', 'f8fef864286a1bbc59f96484074f28d77b1a027f', 'FixedFourAllAudit',
        'LongCycleBounds.fixed_four_all_sizes', '03480b668de5d019c151160440390c5fc4ca380bb5d815eba8791def0a8f206d'),
    5: ('v1.1.0', '70cad373bce521d78d6de9bcff3d29d07fc7fe9f', 'CutoffFiveFinalAudit',
        'LongCycleBounds.FiveCutoff.all_sizes', '7f8b473955b472feb802c68d9e049c547ab88859ee243a337d5cc77a9026f780'),
    6: ('v1.2.0', '46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554', 'SixCutoffAudit',
        'LongCycleBounds.SixCutoff.all_sizes', 'baa9bca94f285968d119941f92d946a2b4be4a212e342e8d599f401f42f90ac6'),
}
SIX_OUTER = '37ec19f48e46eddcaa7a59efb6026b006a61b2a8f753835c585af950bf245527'
SIX_INNER = '605cd388a15d43d5c557605007b9f9e12e1db9cebd11ca80cb9abc33d67004c1'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'

def check_digest(file, expected):
    actual = sha256(file.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f'{file}: expected {expected}, got {actual}')
    print(file.name, actual, flush=True)

def run(*args, cwd):
    subprocess.run(args, cwd=cwd, check=True)

def prepare(k, directory):
    tag, commit, audit, theorem, manifest_hash = PINS[k]
    checkout = directory/'release'
    run('git', 'clone', '--depth', '1', '--branch', tag, REPO, checkout, cwd=directory)
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip() != commit:
        raise ValueError('unexpected tagged commit')
    print(tag, commit, flush=True)
    if k == 6:
        outer = checkout/'cutoff-six/formal/cutoff-six-all-accepted.zip'
        check_digest(outer, SIX_OUTER)
        inner = directory/'source.zip'
        with ZipFile(outer) as z:
            inner.write_bytes(z.read('cutoff-six-all-source.zip'))
        check_digest(inner, SIX_INNER)
        project = directory/'six'
        with ZipFile(inner) as z:
            for name in z.namelist():
                if Path(name).is_absolute() or '..' in Path(name).parts:
                    raise ValueError(name)
            z.extractall(project)
        run('sha256sum','--quiet','-c','SHA256SUMS',cwd=project)
    else:
        project = checkout if k == 4 else checkout/'cutoff-five/formal'
    check_digest(project/'lake-manifest.json', manifest_hash)
    pkgs = json.loads((project/'lake-manifest.json').read_text())['packages']
    if not any(p['name']=='mathlib' and p['rev']==MATHLIB for p in pkgs):
        raise ValueError('unexpected mathlib revision')
    for package in pkgs:
        print(package['name'],package['rev'],flush=True)
    if (project/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        raise ValueError('unexpected Lean toolchain')
    # The upstream verifier extracts the import closure into a fresh project. Reuse its
    # declaration audits and append our independent statement, with the old size explicit.
    check_statement = f"""
#print LongCycles.Allowed
#print LongCycles.excedances
#print LongCycles.enumerator
#print LongCycleFinite.StrictNegativeInterlacing
#print LongCycles.WeakRealInterlacing
#check @{theorem}
#check @LongCycleBounds.Band.actual_general_cycle_row
open LongCycles LongCycleFinite Polynomial
theorem ExternalExcedanceAudit {{m : ℕ}} (hm : {k} ≤ m) :
    (∃ p q : Polynomial ℝ, enumerator m {k} = X * p ∧ enumerator (m+1) {k} = X * q ∧
      StrictNegativeInterlacing p q (m-2)) ∧
    WeakRealInterlacing (enumerator m {k}) (enumerator (m+1) {k}) := by
  have hh : {k+1} ≤ m+1 := by omega
  have h := {theorem} hh
"""
    if k == 4:
        check_statement += """
  refine ⟨⟨_, _, LongCycleBounds.Band.actual_general_cycle_row (by decide) (by omega),
    LongCycleBounds.Band.actual_general_cycle_row (by decide) (by omega), ?_⟩, ?_⟩
  · simpa using h.1
  · simpa using h.2
"""
    else:
        check_statement += f'  simpa [LongCycleFinite.K{k}Prefix.OriginalPair] using h\n'
    module = 'OldSizeVerification'
    check_statement += '#check @ExternalExcedanceAudit\n#print axioms ExternalExcedanceAudit\n'
    (project/f'{module}.lean').write_text((project/f'{audit}.lean').read_text()+check_statement)
    return project, module

if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('cutoff', type=int, choices=PINS)
    ap.add_argument('directory', type=Path)
    args=ap.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    project, module=prepare(args.cutoff,args.directory.resolve())
    run('lean','--version',cwd=project)
    run('lake','--version',cwd=project)
    verifier=project/('scripts/verify_lean.py' if args.cutoff==4 else 'verify_lean.py')
    os.environ['LEAN_NUM_THREADS']='1'
    run('python3','-Bu',verifier,project,module,'--serial',cwd=project)
