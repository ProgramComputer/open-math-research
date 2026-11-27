import FourierPoleDifferentiation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

open scoped Real

/-- The actual annular coefficient has a factor at most 3r over the
normalized inverse pole power. -/
theorem row_pole_coefficient_bound {k : ℕ} (hk : 0 < k) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hcap : R ≤ (1+1/(k:ℝ))*r) (p : ℂ) :
    ‖(R:ℂ)^k/p^(k-1)‖ ≤ (3*r)*‖(r:ℂ)/p‖^(k-1) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hu : R/r ≤ 1+1/(k:ℝ) := (div_le_iff₀ hr).2 hcap
  have hev : (Real.exp (1/(k:ℝ)))^k = Real.exp 1 := by
    rw [← Real.exp_nat_mul,mul_one_div,div_self hkR.ne']
  have hpow : (R/r)^k ≤ 3 := by
    calc
      _ ≤ (1+1/(k:ℝ))^k := pow_le_pow_left₀ (div_nonneg hR.le hr.le) hu k
      _ ≤ (Real.exp (1/(k:ℝ)))^k := by
        apply pow_le_pow_left₀ (by positivity) _ k
        simpa only [add_comm] using Real.add_one_le_exp (1/(k:ℝ))
      _ = Real.exp 1 := hev
      _ ≤ 3 := by linarith only [Real.exp_one_lt_d9]
  have hRk : R^k ≤ 3*r^k :=
    (div_le_iff₀ (pow_pos hr _)).1 (by simpa only [div_pow] using hpow)
  have hrk : r^k = r*r^(k-1) := by
    calc
      r^k = r^((k-1)+1) := by congr 1; omega
      _ = _ := pow_succ' _ _
  simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,abs_of_pos hr]
  calc
    _ ≤ (3*r^k)/‖p‖^(k-1) := div_le_div_of_nonneg_right hRk (by positivity)
    _ = _ := by rw [hrk,div_pow,← mul_div_assoc]; ring

/-- The exact squared pole gap yields the inverse square-root and inverse
gap factors appearing in the Fourier kernels. -/
theorem squared_gap_inverse_factors {x K r R : ℝ} (hx : 0 < x) (hk : 0 < K) (hr : 0 < r)
    {p : ℂ} (hgap : r^2/(K*x) ≤ poleGap p R) :
    (Real.sqrt (poleGap p R))⁻¹ ≤ Real.sqrt (K*x)/r ∧
      (poleGap p R)⁻¹ ≤ K*x/r^2 := by
  have hKx : 0 < K*x := mul_pos hk hx
  have hA : 0 < Real.sqrt (K*x) := Real.sqrt_pos.2 hKx
  have hroot : r/Real.sqrt (K*x) ≤ Real.sqrt (poleGap p R) := by
    apply Real.le_sqrt_of_sq_le
    rwa [div_pow,Real.sq_sqrt hKx.le]
  have hinv := inv_anti₀ (div_pos hr hA) hroot
  have hinv' := inv_anti₀ (div_pos (sq_pos_of_pos hr) hKx) hgap
  exact ⟨hinv.trans_eq (inv_div _ _), hinv'.trans_eq (inv_div _ _)⟩

#print axioms row_pole_coefficient_bound
#print axioms squared_gap_inverse_factors
end OpenMathResearch.LongCycleExcedances
