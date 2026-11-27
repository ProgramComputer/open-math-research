"""Compose the original contour identities and bounds on the shared research pin."""
import argparse
from pathlib import Path
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODULES = (
    ("FourierContourNormalization", ("normalize_contour_split", "normalize_adjacent_real")),
    ("FourierContourReadout", ("signed_contour_readout",)),
    ("FourierPrincipalAlgebra", ("actual_principal_displacement", "normalized_residue_conjugation")),
    ("FourierPairedRows", ("paired_rows_from_contour",)),
    ("FourierSelectedRadius", ("selected_radius_geometry",)),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="a fresh build directory")
    parser.add_argument("--retained-imports", type=Path, help="authenticated upstream objects")
    args = parser.parse_args()
    project = args.project.resolve()
    command = [sys.executable, "-Bu", str(HERE.parent / "fourier-original-errors/check.py"), str(project)]
    if args.retained_imports:
        command.extend(["--retained-imports", str(args.retained_imports.resolve(strict=True))])
    subprocess.run(command, check=True)
    enclosed = runpy.run_path(str(HERE.parent / "fourier-enclosed-residues/check.py"))
    build = enclosed["STABLE"]["build_local"]
    high = enclosed["HIGH"]
    for folder, names in (("uniform-log-tilt", ("UniformDiscreteTilt",)), ("vertical-tilt", enclosed["VERTICAL"])):
        for module in names:
            source = HERE.parent / folder / (module + ".lean")
            staged = project / source.name
            output = project / ".lake/build/lib/lean" / (module + ".olean")
            if not (output.exists() and staged.is_file() and staged.read_bytes() == source.read_bytes()):
                build(project, source, module, ())
    for module in enclosed["WIDE"]:
        namespace = high["ORIGINAL"] if module == "RepositoryWideResidues" else high["GENERIC"]
        high["check_module"](project, HERE.parent / "fourier-enclosed-residues" / (module + ".lean"), namespace)
    for path, step in (("fourier-minor-sums", "compile_minor_sums"),
                       ("fourier-contour-coefficient", "compile_contour_coefficients"),
                       ("fourier-pole-pairing", "compile_enclosed_pairing")):
        runpy.run_path(str(HERE.parent / path / "check.py"))[step](project)
    for module, names in MODULES:
        build(project, HERE / (module + ".lean"), module, names)
    high["check_module"](project, HERE / "RepositoryFourierPairedRows.lean", high["ORIGINAL"])


if __name__ == "__main__":
    main()
