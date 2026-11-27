import ProbabilityErrorBands
import LiteralBinSupport

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability

/-- Rounded-down complete blocks from a slab's lower integer and the total bin.
Nat subtraction supplies zero below the first usable block. -/
def centeredBinIndex (lower b : ℕ) := min 40 (lower-(b+3)/4)

theorem centeredBinIndex_valid {lower b k n t : ℕ} (hlo : lower*k ≤ n) (ht : 4*t ≤ k*b) :
    centeredBinIndex lower b*k ≤ n-t := by
  let r := (b+3)/4
  have hb : b ≤ 4*r := by dsimp [r]; omega
  have ht' : t ≤ r*k := by
    have := Nat.mul_le_mul_left k hb
    nlinarith
  by_cases h : r ≤ lower
  · have he : lower-r+r=lower := Nat.sub_add_cancel h
    have hbr : centeredBinIndex lower b+r ≤ lower := by
      unfold centeredBinIndex
      change min 40 (lower-r)+r ≤ lower
      omega
    have hs := (Nat.mul_le_mul_right k hbr).trans hlo
    rw [Nat.add_mul] at hs
    omega
  · have he : centeredBinIndex lower b = 0 := by
      unfold centeredBinIndex
      change min 40 (lower-r) = 0
      omega
    simp [he]

theorem centeredErrorBound_nonneg (j : ℕ) : 0 ≤ centeredErrorBound j := by
  unfold centeredErrorBound
  split
  · norm_num
  split
  · norm_num
  apply le_min
  · split <;> norm_num
  · positivity

/-- Joint degree support selects the same probability bound as the rational
checker at every occupied configuration, including degrees past the row size. -/
theorem centered_probability_on_bin {m n lower b t : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d)
    (hk : 100 ≤ m+1) (hlo : lower*(m+1) ≤ n) (ht : 4*t ≤ (m+1)*b) :
    ((m:ℝ)+1)*|cutoffWeight (m+1) d (n-t)-Real.exp (-cycleHarmonic m)| ≤
      centeredErrorBound (centeredBinIndex lower b) :=
  probability_error_bands hd hk (centeredBinIndex_valid hlo ht)

#print axioms centeredBinIndex_valid
#print axioms centered_probability_on_bin
end OpenMathResearch.LongCycleExcedances
