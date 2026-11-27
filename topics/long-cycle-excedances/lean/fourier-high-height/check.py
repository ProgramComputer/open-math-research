#!/usr/bin/env python3
"""Build and audit the high-height contraction on the common repository pin."""
import argparse
from hashlib import sha256
from pathlib import Path
import re
import runpy
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
STABLE = runpy.run_path(str(HERE.parent / 'fourier-stable' / 'check-real-axis.py'))
COMMON = STABLE['COMMON']
GENERIC = 'OpenMathResearch.LongCycleExcedances.'
ORIGINAL = 'RepositoryQuotientAudit.'
MODULES = (
    (HERE.parent / 'vertical-tilt' / 'ComplexDiscreteMoment.lean', GENERIC),
    (HERE.parent / 'vertical-tilt' / 'RepositoryLogTiltDiscrete.lean', ORIGINAL),
    *((HERE / f'{name}.lean', GENERIC) for name in (
        'PoissonTilts', 'HighHeightScalars', 'PositiveFrequency', 'PoissonRadiusBounds',
        'HighHeightContraction', 'HighHeightLogSource', 'FrequencyPrefix',
        'FrequencyMajorants', 'HighHeightNumerator', 'HighHeightPointAdapter',
    )),
    (HERE / 'RepositoryHighHeightNumerator.lean', ORIGINAL),
)


def check_module(project, original, namespace):
    module = original.stem
    source = project / original.name
    shutil.copyfile(original, source)
    output = project / '.lake/build/lib/lean' / f'{module}.olean'
    print(f'Compile {module} input-sha256={sha256(source.read_bytes()).hexdigest()}', flush=True)
    build = subprocess.run(
        ['lake', 'env', 'lean', '-o', str(output), str(source)],
        cwd=project, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    print(build.stdout, end='', flush=True)
    build.check_returncode()
    expected = re.findall(r'^#print axioms (\w+)$', original.read_text(), re.M)
    if not expected:
        raise ValueError(f'No named axiom checks in {module}')
    for theorem in expected:
        full = re.escape(namespace + theorem)
        match = re.findall(rf"^'{full}' depends on axioms:\s*\[([^\]]*)\]$", build.stdout, re.M)
        if len(match) != 1 or {axiom.strip() for axiom in match[0].split(',')} - COMMON['ALLOWED']:
            raise ValueError(f'Missing declaration or unexpected axioms for {namespace + theorem}')
    COMMON['run'](project, 'lake', 'env', 'leanchecker', '--verbose', module)
    print(f'kernel_replay_exit=0 {module}', flush=True)
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    parser.add_argument('--retained-imports', type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    imports = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    STABLE['main'](project, True, imports)
    count = sum(check_module(project, file, namespace) for file, namespace in MODULES)
    print(f'PASS: {count} high-height declarations audited', flush=True)


if __name__ == '__main__':
    main()
