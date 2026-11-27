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
    degree = len(row["windows"])
    parts = [f"private def tail{degree} : List Window := []",
             f"private theorem signs{degree} : signsOK p q 0 tail{degree} = true := rfl"]
    for index in reversed(range(degree)):
        left, right = row["windows"][index]
        exponent = degree - index
        prior = index + 1
        parts.append(f"""private def window{index} : Window := ⟨{dyadic(left)}, {dyadic(right)}⟩
private def tail{index} : List Window := window{index} :: tail{prior}
private theorem signs{index} : signsOK p q {exponent} tail{index} = true := by
  have here : windowOK p q {exponent} window{index} = true := by decide +kernel
  change (windowOK p q {exponent} window{index} &&
    signsOK p q {exponent - 1} tail{prior}) = true
  simp only [here, signs{prior}, Bool.and_self]""")
    windows = "\n\n".join(parts)
    return f"""import LongCycleFinite.Assembly

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace OpenMathResearch.LongCycleExcedances.FirstSplitCase{k}
open Polynomial LongCycleFinite

private def p : List ℤ := {int_list(row["p"])}
private def q : List ℤ := {int_list(row["q"])}
private def outer : LongCycleFinite.Dyadic := {dyadic(row["outer"])}
{windows}

private theorem checked : caseOK p q outer tail0 = true := by
  have boundary : boundaryOK p q outer {degree} = true := by decide +kernel
  have ordered : orderOK outer tail0 = true := by decide +kernel
  change (boundaryOK p q outer {degree} && orderOK outer tail0 &&
    signsOK p q {degree} tail0) = true
  simp only [boundary, ordered, signs0, Bool.and_self]

theorem strict : StrictNegativeInterlacing (firstP {k}) (firstQ {k}) (2 * {k} - 3) := by
  have old : expandCoeffs (2 * {k} - 3) p = descentCoeffs (2 * {k} - 2) := by decide +kernel
  have next : expandCoeffs (2 * {k} - 2) q = qCoeffs {k} := by decide +kernel
  exact firstSplitStrict_of_checked (by decide : 3 ≤ {k})
    (rfl : tail0.length = {k} - 2) checked old next

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
