"""Check the simultaneous numerator and denominator estimates on the selected circle."""
import argparse
from pathlib import Path
import re
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
STABLE = HERE.parent / "fourier-stable"
CIRCLE = HERE.parent / "fourier-circle"
DRIVER = runpy.run_path(str(STABLE / "check-real-axis.py"))
CIRCLE_REPORTS = runpy.run_path(str(CIRCLE / "check.py"))["THEOREMS"]
MODULES = [
    (STABLE, "FourierDiskLog", ("diskLogisticLog_deriv", "diskLogisticLog_normalized")),
    *((CIRCLE, name, CIRCLE_REPORTS[name]) for name in
      ("FourierCircleChoice", "FourierLogarithmicGap", "FourierExponentialGap", "FourierOriginalDenominators")),
    (HERE, "FourierAmplitudeComparison", ("annular_amplitude_from_contraction", "disk_amplitude_comparison")),
    (HERE, "FourierAmplitudeScalars", ("selected_gap_is_small", "selected_ratio_factor",
                                      "selected_ratio_regimes", "selected_amplitude_regimes")),
    (HERE, "FourierSelectedAmplitude", ("selected_circle_amplitude",)),
]


def compile_amplitude(project):
    failed = set()
    for folder, name, reports in MODULES:
        source = folder / f"{name}.lean"
        missing = set(re.findall(r"^import ([\w.]+)", source.read_text(), re.M)) & failed
        if missing:
            print(f"Skipped {name}: missing {sorted(missing)}", flush=True)
            failed.add(name)
            continue
        try:
            DRIVER["build_local"](project, source, name, reports)
        except subprocess.CalledProcessError:
            failed.add(name)
    if failed:
        raise RuntimeError(f"Incomplete amplitude checks: {sorted(failed)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a fresh check directory")
    parser.add_argument("--retained-imports", type=Path, help="authenticated upstream object archive")
    args = parser.parse_args()
    project = args.project.resolve()
    retained = args.retained_imports.resolve(strict=True) if args.retained_imports else None
    DRIVER["main"](project, True, retained)
    compile_amplitude(project)
