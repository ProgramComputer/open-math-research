import FarPoleTruncation
import HighAngleScalar

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- A pole contribution truncated to the coefficient indices strictly below q,
in the normalization with the principal radius to power q+1. -/
def normalizedPolePrefix (T : ℕ → ℂ) (q : ℕ) (r : ℝ) (w : ℂ) : ℂ :=
  (r:ℂ)^(q+1) * ∑ j ∈ range q, T j * (1 / w^(q-j+1))

/-- Use the full numerator series for poles in the inner group. All other
poles have zero approximant. -/
def normalizedPoleApprox (T : ℕ → ℂ) (q : ℕ) (r R₀ : ℝ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ R₀ then ((r:ℂ)/w)^(q+1) * ∑' j, T j * w^j else 0

private theorem normalizedPolePrefix_eq (T : ℕ → ℂ) (q : ℕ) (r : ℝ)
    {w : ℂ} (hw : w ≠ 0) :
    normalizedPolePrefix T q r w =
      ((r:ℂ)/w)^(q+1) * ∑ j ∈ range q, T j * w^j := by
  unfold normalizedPolePrefix
  rw [mul_sum, mul_sum, div_pow]
  apply sum_congr rfl
  intro j hj
  have he : q+1 = (q-j+1)+j := by have := mem_range.mp hj; omega
  rw [show w^(q+1) = w^(q-j+1)*w^j by rw [←pow_add,←he]]
  field_simp [hw] <;> ring

/-- Truncation error at an enclosed pole, using the fixed outer Taylor radius. -/
theorem nested_near_pole_error (T : ℕ → ℂ) (q : ℕ) {A r R₀ Rstar : ℝ} {w : ℂ}
    (hA : 0 ≤ A) (hr : 0 < r) (hnear : r ≤ ‖w‖) (hin : ‖w‖ ≤ R₀) (hR : R₀ < Rstar)
    (hT : ∀ j, ‖T j‖ ≤ A/Rstar^j) :
    ‖normalizedPolePrefix T q r w - normalizedPoleApprox T q r R₀ w‖ ≤
      (A*(r/Rstar)^q*(r/‖w‖))/(1-R₀/Rstar) := by
  let W := ‖w‖
  have hW : 0 < W := hr.trans_le hnear
  have hRstar : 0 < Rstar := (hW.trans_le hin).trans hR
  have hρ : W/Rstar < 1 := (div_lt_one hRstar).2 (hin.trans_lt hR)
  have hρ₀ : 0 ≤ W/Rstar := div_nonneg hW.le hRstar.le
  have hdom (j : ℕ) : ‖T j*w^j‖ ≤ A*(W/Rstar)^j := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (A/Rstar^j)*W^j := mul_le_mul_of_nonneg_right (hT j) (by positivity)
      _ = _ := by rw [div_pow]; ring
  have htail := (taylor_tail_majorant (fun j => T j*w^j) hA hρ₀ hρ hdom q).2
  have hw : w ≠ 0 := norm_pos_iff.mp hW
  rw [normalizedPolePrefix_eq T q r hw,normalizedPoleApprox,if_pos hin,←mul_sub,
    norm_mul,norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,norm_sub_rev]
  have hM : R₀/Rstar < 1 := (div_lt_one hRstar).2 hR
  have hden : 0 < 1-R₀/Rstar := sub_pos.mpr hM
  have hden' : 1-R₀/Rstar ≤ 1-W/Rstar :=
    sub_le_sub_left (div_le_div_of_nonneg_right hin hRstar.le) _
  calc
    _ ≤ (r/W)^(q+1)*(A*(W/Rstar)^q/(1-W/Rstar)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (A*(r/Rstar)^q*(r/W))/(1-W/Rstar) := by
      rw [pow_succ (r/W),show (r/Rstar)^q = (r/W)^q*(W/Rstar)^q by
        rw [←mul_pow]
        congr 1
        field_simp [hW.ne',hRstar.ne']]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) hden hden'

/-- Fixed-radius bound for the omitted outer pole, leaving an inverse square
in its modulus for the subsequent lattice sum. -/
theorem nested_far_pole_error (T : ℕ → ℂ) {q : ℕ} (hq : 0 < q)
    {A r R₁ R₀ Rstar : ℝ} {w : ℂ} (hA : 0 ≤ A) (hr : 0 < r) (h₁ : r < R₁)
    (h₀ : R₁ < R₀) (hstar : R₀ < Rstar) (hout : R₀ < ‖w‖)
    (hT : ∀ j, ‖T j‖ ≤ A/Rstar^j) :
    ‖normalizedPolePrefix T q r w - normalizedPoleApprox T q r R₀ w‖ ≤
      (A*(r/R₁)^(q-1)*(r/‖w‖)^2)/(1-R₁/R₀) := by
  let W := ‖w‖
  have hR₁ : 0 < R₁ := hr.trans h₁
  have hR₀ : 0 < R₀ := hR₁.trans h₀
  have hW : 0 < W := hR₀.trans hout
  have hT₁ (j : ℕ) (_ : j < q) : ‖T j‖ ≤ A/R₁^j :=
    (hT j).trans (div_le_div_of_nonneg_left hA (pow_pos hR₁ _)
      (pow_le_pow_left₀ hR₁.le (h₀.trans hstar).le _))
  have h := norm_far_pole_truncation_le T q hA hR₁ (h₀.trans hout) hT₁
  rw [normalizedPoleApprox,if_neg (not_le.mpr hout),sub_zero,normalizedPolePrefix,
    norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hd : 0 < 1-R₁/R₀ := sub_pos.mpr ((div_lt_one hR₀).2 h₀)
  have hd' : 1-R₁/R₀ ≤ 1-R₁/W :=
    sub_le_sub_left (div_le_div_of_nonneg_left hR₁.le hR₀ hout.le) _
  calc
    _ ≤ r^(q+1)*((A/(R₁^(q-1)*W^2))/(1-R₁/W)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (A*(r/R₁)^(q-1)*(r/W)^2)/(1-R₁/W) := by
      rw [show r^(q+1) = r^(q-1)*r^2 by rw [←pow_add,show q-1+2=q+1 by omega],
        div_pow,div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hd hd'

/-- Two fixed nested radii give a uniform one-pole error with an inverse-square
lattice factor. This avoids choosing any separating contour. -/
theorem nested_pole_radii_error (T : ℕ → ℂ) {q : ℕ} (hq : 0 < q)
    {A r R₁ R₀ Rstar : ℝ} {w : ℂ} (hA : 0 ≤ A) (hr : 0 < r) (h₁ : r < R₁)
    (h₀ : R₁ < R₀) (hstar : R₀ < Rstar) (hw : r ≤ ‖w‖)
    (hT : ∀ j, ‖T j‖ ≤ A/Rstar^j) :
    ‖normalizedPolePrefix T q r w - normalizedPoleApprox T q r R₀ w‖ ≤
      (if ‖w‖ ≤ R₀ then (R₀/Rstar)/(1-R₀/Rstar) else 1/(1-R₁/R₀)) *
        (A*(r/R₁)^(q-1)*(r/‖w‖)^2) := by
  let W := ‖w‖
  have hW : 0 < W := hr.trans_le hw
  have hR₁ : 0 < R₁ := hr.trans h₁
  have hR₀ : 0 < R₀ := hR₁.trans h₀
  have hRstar : 0 < Rstar := hR₀.trans hstar
  by_cases hin : W ≤ R₀
  · rw [if_pos hin]
    have h := nested_near_pole_error T q hA hr hw hin hstar hT
    have hp : (r/Rstar)^(q-1) ≤ (r/R₁)^(q-1) :=
      pow_le_pow_left₀ (div_nonneg hr.le hRstar.le)
        (div_le_div_of_nonneg_left hr.le hR₁ (h₀.trans hstar).le) _
    have hB : 0 < 1-R₀/Rstar := sub_pos.mpr ((div_lt_one hRstar).2 hstar)
    have hWR : W/Rstar ≤ R₀/Rstar := div_le_div_of_nonneg_right hin hRstar.le
    refine h.trans ?_
    calc
      _ = ((W/Rstar)/(1-R₀/Rstar))*(A*(r/Rstar)^(q-1)*(r/W)^2) := by
        change (A*(r/Rstar)^q*(r/W))/(1-R₀/Rstar) = _
        have he : (r/Rstar)*(r/W) = (W/Rstar)*(r/W)^2 := by
          field_simp [hW.ne',hRstar.ne'] <;> ring
        rw [show (r/Rstar)^q = (r/Rstar)^(q-1)*(r/Rstar) by
          rw [←pow_succ,show q-1+1=q by omega]]
        calc
          _ = (A*(r/Rstar)^(q-1)*((r/Rstar)*(r/W)))/(1-R₀/Rstar) := by ring
          _ = _ := by rw [he]; ring
      _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hWR hB.le)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (by positivity))
        (by positivity) (by positivity)
  · rw [if_neg hin]
    exact (nested_far_pole_error T hq hA hr h₁ h₀ hstar (lt_of_not_ge hin) hT).trans_eq
      (by ring)

/-- A single majorant for both sides, convenient when summing over poles. -/
theorem nested_pole_radii_error_uniform (T : ℕ → ℂ) {q : ℕ} (hq : 0 < q)
    {A r R₁ R₀ Rstar : ℝ} {w : ℂ} (hA : 0 ≤ A) (hr : 0 < r) (h₁ : r < R₁)
    (h₀ : R₁ < R₀) (hstar : R₀ < Rstar) (hw : r ≤ ‖w‖)
    (hT : ∀ j, ‖T j‖ ≤ A/Rstar^j) :
    ‖normalizedPolePrefix T q r w - normalizedPoleApprox T q r R₀ w‖ ≤
      max ((R₀/Rstar)/(1-R₀/Rstar)) (1/(1-R₁/R₀)) *
        (A*(r/R₁)^(q-1)*(r/‖w‖)^2) := by
  apply (nested_pole_radii_error T hq hA hr h₁ h₀ hstar hw hT).trans
  have hR₁ : 0 < R₁ := hr.trans h₁
  exact mul_le_mul_of_nonneg_right (by
    split
    · exact le_max_left _ _
    · exact le_max_right _ _)
    (mul_nonneg (mul_nonneg hA (pow_nonneg (div_nonneg hr.le hR₁.le) _)) (sq_nonneg _))

#print axioms nested_near_pole_error
#print axioms nested_far_pole_error
#print axioms nested_pole_radii_error
#print axioms nested_pole_radii_error_uniform
end OpenMathResearch.LongCycleExcedances
