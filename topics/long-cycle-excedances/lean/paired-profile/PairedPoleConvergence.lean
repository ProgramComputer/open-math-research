import PairedPoleFamily
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped PowerSeries

private theorem norm_paired_denom_lower (C S : ℝ) (q : ℤ) :
    |2*(q:ℝ)+1| * |S| ≤ ‖pairedPoleDenom C S q‖ := by
  have h : (pairedPoleDenom C S q).im = (2*(q:ℝ)+1)*S := by
    simp [pairedPoleDenom, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re]
  rw [←abs_mul,←h]
  exact Complex.abs_im_le_norm _

/-- Absolute convergence at every fixed coefficient of degree at least two. -/
theorem summable_paired_pole_power_norm (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun q : ℤ => ‖(pairedPoleDenom C S q)⁻¹‖^p) := by
  have hs : Summable (fun q : ℤ => 1 / |(q:ℝ)+1/2|^p) := by
    simpa using (Real.summable_one_div_int_add_rpow (1/2) (p:ℝ)).mpr
      (by exact_mod_cast (show 1 < p by omega))
  let c := 2*|S|
  have hc : 0 < c := mul_pos (by norm_num) (abs_pos.mpr hS)
  apply Summable.of_nonneg_of_le (fun q => pow_nonneg (norm_nonneg _) p) _ (hs.mul_left ((1/c)^p))
  intro q
  have hn : 0 < |(q:ℝ)+1/2| := by
    apply abs_pos.mpr
    intro h
    have hi : (2*q+1:ℤ)=0 := by
      exact_mod_cast (show 2*(q:ℝ)+1=0 by linarith)
    omega
  have hbound : c*|(q:ℝ)+1/2| ≤ ‖pairedPoleDenom C S q‖ := by
    have h := norm_paired_denom_lower C S q
    rw [show 2*(q:ℝ)+1=2*((q:ℝ)+1/2) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    dsimp [c]
    nlinarith only [h]
  simp only [norm_inv, one_div, ← inv_pow, ← mul_pow, ← mul_inv]
  simpa only [one_div] using pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    ((inv_le_inv₀ ((mul_pos hc hn).trans_le hbound) (mul_pos hc hn)).mpr hbound) p

/-- One odd-index weight costs at most one pole power, so the derivative
majorant is summable at all degrees at least three. -/
theorem summable_paired_pole_first_moment (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    {p : ℕ} (hp : 3 ≤ p) :
    Summable (fun q : ℤ => |2*(q:ℝ)+1| * ‖(pairedPoleDenom C S q)⁻¹‖^p) := by
  have hSp := abs_pos.mpr hS
  have hs := (summable_paired_pole_power_norm C hS (p := p-1) (by omega)).mul_left (1/|S|)
  apply Summable.of_nonneg_of_le (fun q => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _)) _ hs
  intro q
  have hw : 0 < ‖pairedPoleDenom C S q‖ := norm_pos_iff.mpr (pairedPoleDenom_ne_zero C hS q)
  have hm : |2*(q:ℝ)+1| * ‖(pairedPoleDenom C S q)⁻¹‖ ≤ 1/|S| := by
    rw [norm_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ hw).mpr
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hSp).mpr (norm_paired_denom_lower C S q)
  calc
    _ = (|2*(q:ℝ)+1| * ‖(pairedPoleDenom C S q)⁻¹‖) *
      ‖(pairedPoleDenom C S q)⁻¹‖^(p-1) := by
        rw [show ‖(pairedPoleDenom C S q)⁻¹‖^p =
          ‖(pairedPoleDenom C S q)⁻¹‖^(p-1)*‖(pairedPoleDenom C S q)⁻¹‖ by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (pow_nonneg (norm_nonneg _) _)

def pairedCycleLog (k : ℕ) (C S : ℝ) (q : ℤ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun p => if k ≤ p then ((pairedPoleDenom C S q)⁻¹)^p/(p:ℂ) else 0

/-- The coefficientwise limit uses the net of all finite pole subsets. -/
theorem hasSum_paired_cycle_log_coeff (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (p : ℕ) :
    HasSum (fun q : ℤ => PowerSeries.coeff (R := ℂ) p (pairedCycleLog k C S q))
      (if k ≤ p then (∑' q : ℤ, ((pairedPoleDenom C S q)⁻¹)^p)/(p:ℂ) else 0) := by
  by_cases hp : k ≤ p
  · have hs : Summable (fun q : ℤ => ((pairedPoleDenom C S q)⁻¹)^p) :=
      Summable.of_norm (by simpa only [norm_pow] using summable_paired_pole_power_norm C hS (hk.trans hp))
    simpa only [pairedCycleLog, PowerSeries.coeff_mk, if_pos hp, div_eq_mul_inv] using
      hs.hasSum.mul_right ((p:ℂ)⁻¹)
  · simp only [pairedCycleLog, PowerSeries.coeff_mk, if_neg hp]
    exact hasSum_zero

#print axioms summable_paired_pole_power_norm
#print axioms summable_paired_pole_first_moment
#print axioms hasSum_paired_cycle_log_coeff
end OpenMathResearch.LongCycleExcedances
