"""Translate frozen dyadic data into independently checked Lean declarations."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CUTOFFS = range(8, 55)


def int_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def dyadic(point):
    numerator, exponent = point
    return f"⟨{numerator}, {exponent}⟩"


def emit_case(row):
    k = row["k"]
    windows = ",\n  ".join(f"⟨{dyadic(left)}, {dyadic(right)}⟩"
                           for left, right in row["windows"])
    return f"""import LongCycleFinite.Assembly

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace OpenMathResearch.LongCycleExcedances.FirstSplitCase{k}
open Polynomial LongCycleFinite

private def p : List ℤ := {int_list(row["p"])}
private def q : List ℤ := {int_list(row["q"])}
private def outer : Dyadic := {dyadic(row["outer"])}
private def windows : List Window := [
  {windows}]

theorem strict : StrictNegativeInterlacing (firstP {k}) (firstQ {k}) (2 * {k} - 3) := by
  have checked : caseOK p q outer windows = true := by decide +kernel
  have old : expandCoeffs (2 * {k} - 3) p = descentCoeffs (2 * {k} - 2) := by decide +kernel
  have next : expandCoeffs (2 * {k} - 2) q = qCoeffs {k} := by decide +kernel
  exact firstSplitStrict_of_checked (by decide : 3 ≤ {k})
    (rfl : windows.length = {k} - 2) checked old next

#print axioms strict
end OpenMathResearch.LongCycleExcedances.FirstSplitCase{k}
"""


def emit_cases(target):
    rows = [json.loads(line) for line in (HERE / "first-split.jsonl").read_text().splitlines()]
    if [row["k"] for row in rows] != list(CUTOFFS):
        raise ValueError("Expected one row for each cutoff from 8 to 54")
    for row in rows:
        cutoff = row["k"]
        (target / f"FirstSplitCase{cutoff}.lean").write_text(emit_case(row))

    imports = "\n".join(f"import FirstSplitCase{k}" for k in CUTOFFS)
    cases = "\n".join(f"  · exact FirstSplitCase{k}.strict" for k in CUTOFFS)
    (target / "FirstSplitFinite.lean").write_text(f"""{imports}

namespace OpenMathResearch.LongCycleExcedances
open Polynomial LongCycleFinite

theorem finite_first_split_strict {{k : ℕ}} (lo : 8 ≤ k) (hi : k ≤ 54) :
    StrictNegativeInterlacing (firstP k) (firstQ k) (2*k-3) := by
  interval_cases k
{cases}

#print axioms finite_first_split_strict
end OpenMathResearch.LongCycleExcedances
""")


if __name__ == "__main__":
    import sys
    target = Path(sys.argv[1])
    target.mkdir(parents=True, exist_ok=True)
    emit_cases(target)
