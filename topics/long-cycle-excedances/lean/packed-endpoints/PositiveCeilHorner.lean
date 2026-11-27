import RoundedHorner
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open Finset

/-- Integer upper bound by positive Horner evaluation and ceiling at every step. -/
def upperHorner (p : ℤ) (d : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: tail => a - (-(p * upperHorner p d tail) / (d:ℤ))

theorem upperHorner_cons (p a : ℤ) (d : ℕ) (cs : List ℤ) :
    upperHorner p d (a::cs) = a + ⌈((p:ℚ)/d) * (upperHorner p d cs : ℚ)⌉ := by
  rw [div_mul_eq_mul_div, ← Int.cast_mul, Rat.ceil_intCast_div_natCast, upperHorner]
  ring

theorem horner_positive_le (p : ℤ) (d : ℕ) (cs : List ℤ) (hy : 0 ≤ (p:ℚ)/d) :
    horner (-((p:ℚ)/d)) cs ≤ (upperHorner p d cs : ℚ) := by
  induction cs with
  | nil => simp [horner, upperHorner]
  | cons a cs ih =>
    rw [upperHorner_cons, horner, neg_mul, sub_neg_eq_add, Int.cast_add]
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left ih hy).trans (Int.le_ceil _))

def uncertainty (p : ℤ) (d : ℕ) (cs : List ℤ) : ℤ :=
  -(-(upperHorner p d cs) / 2^36)

theorem uncertainty_upper (p : ℤ) (d : ℕ) (c : ℕ → ℤ) (w : ℕ) (hy : 0 ≤ (p:ℚ)/d) :
    (∑ i ∈ range w, (c i : ℚ) * ((p:ℚ)/d)^i)/2^36 ≤
      (uncertainty p d (firstCoeffs c w) : ℚ) := by
  let cs := firstCoeffs c w
  have hu := horner_positive_le p d cs hy
  rw [horner_first, neg_neg] at hu
  have hdiv := div_le_div_of_nonneg_right hu (by positivity : (0:ℚ) ≤ 2^36)
  refine hdiv.trans ?_
  have h := Int.le_ceil ((upperHorner p d cs : ℚ) / (2^36:ℕ))
  rw [Rat.ceil_intCast_div_natCast] at h
  simpa only [uncertainty, cs, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The integer lower bound pays for both signed Horner rounding and the full
coefficient uncertainty in a compressed row. -/
theorem compressed_lower {σ T L U H B : ℝ} (hs : |σ|=1)
    (perturb : |T-L| ≤ U) (upper : U ≤ B) (rounding : σ*H-2 ≤ σ*L) :
    σ*H-2-B ≤ σ*T := by
  have h : |σ*(T-L)| ≤ B := by simpa [abs_mul, hs] using perturb.trans upper
  have low := (abs_le.mp h).1
  linarith [show σ*(T-L)=σ*T-σ*L by ring]

/-- With a relative coefficient enclosure, the executable integer margin is a
lower bound for the signed value of the true prefix. -/
theorem compressed_integer_margin (p s : ℤ) (d w : ℕ) (c : ℕ → ℤ)
    (hy : 0 ≤ (p:ℚ)/d) (hy' : (p:ℚ)/d ≤ 1/2) (hs : |(s:ℚ)|=1)
    (T : ℝ) (perturb :
      |T - ∑ i ∈ range w, (c i : ℝ)*(-(((p:ℚ)/d : ℚ):ℝ))^i| ≤
        (1/(2:ℝ)^36)*∑ i ∈ range w, (c i : ℝ)*((((p:ℚ)/d : ℚ):ℝ))^i) :
    ((s*roundedRatio p d (firstCoeffs c w) - 2 - uncertainty p d (firstCoeffs c w) : ℤ) : ℝ)
      ≤ (s:ℝ)*T := by
  let y := (p:ℚ)/d
  let cs := firstCoeffs c w
  have hlo := signed_lower hy hy' hs cs
  rw [← roundedRatio_eq p d] at hlo
  change (s:ℚ)*(roundedRatio p d cs : ℚ)-2 ≤ (s:ℚ)*horner y (firstCoeffs c w) at hlo
  rw [horner_first] at hlo
  have cast_le {u v : ℚ} (h : u ≤ v) : (u:ℝ) ≤ (v:ℝ) := by exact_mod_cast h
  have hrounded : (s:ℝ)*(roundedRatio p d cs : ℝ)-2 ≤
      (s:ℝ)*∑ i ∈ range w, (c i : ℝ)*(-(y:ℝ))^i := by
    have h := cast_le hlo
    push_cast at h
    exact h
  have hu := uncertainty_upper p d c w hy
  change (∑ i ∈ range w, (c i : ℚ)*y^i)/2^36 ≤ (uncertainty p d cs : ℚ) at hu
  have hupper : (∑ i ∈ range w, (c i : ℝ)*(y:ℝ)^i)/(2:ℝ)^36 ≤
      (uncertainty p d cs : ℝ) := by
    have h := cast_le hu
    push_cast at h
    exact h
  rw [← one_div_mul_eq_div] at hupper
  push_cast
  exact compressed_lower (by exact_mod_cast hs) perturb hupper hrounded

#print axioms compressed_integer_margin
#print axioms upperHorner_cons
#print axioms horner_positive_le
#print axioms uncertainty_upper
#print axioms compressed_lower
end OpenMathResearch.LongCycleExcedances.IntegerSign
