import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open Finset

def rounded (y : ℚ) : List ℤ → ℤ
  | [] => 0
  | a :: tail => a - ⌊y * (rounded y tail : ℚ)⌋

def horner (y : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: tail => a - y * horner y tail

/-- Integer implementation for dyadic and other rational witnesses. -/
def roundedRatio (p : ℤ) (D : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: tail => a - p * roundedRatio p D tail / (D : ℤ)

theorem roundedRatio_eq (p : ℤ) (D : ℕ) (cs : List ℤ) :
    roundedRatio p D cs = rounded ((p : ℚ) / (D : ℚ)) cs := by
  induction cs with
  | nil => rfl
  | cons a tail ih =>
    simp only [roundedRatio, rounded, ← ih]
    rw [div_mul_eq_mul_div, ← Int.cast_mul, Rat.floor_intCast_div_natCast]

theorem rounded_error {y : ℚ} (hy : 0 ≤ y) (hu : y ≤ 1/2) (cs : List ℤ) :
    |(rounded y cs : ℚ) - horner y cs| ≤ 2 := by
  induction cs with
  | nil => simp [rounded, horner]
  | cons a tail ih =>
    obtain ⟨hl, hr⟩ := abs_le.mp ih
    have lo := mul_le_mul_of_nonneg_left hl hy
    have hi := mul_le_mul_of_nonneg_left hr hy
    have floorLo := Int.floor_le (y * (rounded y tail : ℚ))
    have floorHi := Int.lt_floor_add_one (y * (rounded y tail : ℚ))
    simp only [rounded, horner, Int.cast_sub]
    apply abs_le.mpr
    constructor <;> linarith

theorem signed_lower {y σ : ℚ} (hy : 0 ≤ y) (hu : y ≤ 1/2) (hs : |σ|=1)
    (cs : List ℤ) : σ * (rounded y cs : ℚ) - 2 ≤ σ * horner y cs := by
  have e := rounded_error hy hu cs
  have e' : |σ * ((rounded y cs : ℚ) - horner y cs)| ≤ 2 := by
    simpa [abs_mul, hs] using e
  have u := (abs_le.mp e').2
  linarith

def firstCoeffs (c : ℕ → ℤ) : ℕ → List ℤ
  | 0 => []
  | w+1 => c 0 :: firstCoeffs (fun i => c (i+1)) w

theorem horner_first (y : ℚ) (c : ℕ → ℤ) (w : ℕ) :
    horner y (firstCoeffs c w) = ∑ i ∈ range w, (c i : ℚ) * (-y)^i := by
  induction w generalizing c with
  | zero => simp [firstCoeffs, horner]
  | succ w ih =>
    rw [firstCoeffs, horner, ih, sum_range_succ']
    simp only [pow_zero, mul_one, pow_succ]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    ring

#print axioms roundedRatio_eq
#print axioms rounded_error
#print axioms signed_lower
#print axioms horner_first
end OpenMathResearch.LongCycleExcedances.IntegerSign
