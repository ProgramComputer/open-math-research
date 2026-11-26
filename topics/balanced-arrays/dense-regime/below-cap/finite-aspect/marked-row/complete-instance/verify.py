"""Replay the component certificates and check coverage for the finite instance."""
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
MARKED = HERE.parent


def replay(script, *arguments, expected=None):
    command = [sys.executable, "-IB", str(script), *arguments]
    print(f"Running {script.relative_to(MARKED.parent)} {' '.join(arguments)}", flush=True)
    output = subprocess.check_output(command, cwd=script.parent, text=True)
    if expected is not None and output != (HERE / expected).read_text():
        raise ValueError(f"Recorded output differs for {script.name}")
    print(output.rstrip(), flush=True)


def main():
    for script in (MARKED.parent / "verify.py", MARKED.parent / "upper-edge/verify.py",
                   MARKED / "verify.py", MARKED / "independent/verify.py",
                   MARKED / "mixed-phase/verify.py", MARKED / "mixed-phase/replay/verify.py"):
        replay(script)
    replay(HERE / "centered.py", "--transition", expected="centered-output.txt")
    replay(HERE / "phase_order.py", expected="phase-order-output.txt")
    degree = 1_000_000 * 127_000 // 250_000
    intervals = [(1, 505661), (505662, 506470), (506471, 507300),
                 (507300, 507905), (507905, degree-1)]
    next_index = 1
    for first, last in intervals:
        assert first <= next_index <= last+1
        next_index = last+1
    assert next_index == degree == 508000
    print(f"All {degree-1} internal indices are covered; degree {degree}.")


if __name__ == "__main__":
    main()
