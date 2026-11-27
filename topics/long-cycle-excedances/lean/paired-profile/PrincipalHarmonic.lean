import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

def cycleHarmonic (m : ℕ) : ℝ := ∑ i ∈ range m, 1/((i:ℝ)+1)

private theorem harmonic_log_step (x : ℝ) (hx : 0 < x) :
    1/(x+1) ≤ log (x+1)-log x := by
  have hp : 0 < x+1 := by positivity
  have hh := log_le_sub_one_of_pos (div_pos hx hp)
  rw [Real.log_div hx.ne' hp.ne'] at hh
  have hfrac : x/(x+1)-1= -(1/(x+1)) := by field_simp <;> ring
  linarith

private theorem harmonic_anchor {m : ℕ} (hm : 20 ≤ m) :
    cycleHarmonic m ≤ 18/5 + log (m:ℝ) - log 20 := by
  induction m,hm using Nat.le_induction with
  | base =>
    have hh : cycleHarmonic 20 ≤ 18/5 := by
      norm_num [cycleHarmonic,Finset.sum_range_succ]
    norm_num
    linarith
  | succ m hm ih =>
    have hp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hh := harmonic_log_step m hp
    rw [cycleHarmonic,sum_range_succ,←cycleHarmonic]
    push_cast
    linarith

private theorem exp_anchor : exp (18/5) < 110/3 := by
  have he : exp 1 < (2719/1000:ℝ) := by linarith only [Real.exp_one_lt_d9]
  have hp : (exp 1)^18 < (2719/1000:ℝ)^18 := pow_lt_pow_left₀ he (by positivity) (by decide)
  have hprec : (2719/1000:ℝ)^18 < (110/3:ℝ)^5 := by norm_num
  have heq : (exp (18/5))^5 = (exp 1)^18 := by
    rw [←exp_nat_mul,←exp_nat_mul]
    norm_num
  by_contra! hbad
  exact (not_lt_of_ge (heq ▸ pow_le_pow_left₀ (by norm_num) hbad 5)) (hp.trans hprec)

/-- A twenty-term rational anchor yields the harmonic normalization in the principal residue. -/
theorem principal_harmonic_prefactor {k : ℕ} (hk : 21 ≤ k) :
    12/11 < 2*(k:ℝ)*exp (-cycleHarmonic (k-1)) := by
  let m := k-1
  have hm : 20 ≤ m := by dsimp [m]; omega
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hexp := exp_le_exp.mpr (harmonic_anchor hm)
  rw [exp_sub,exp_add,exp_log hm0,exp_log (by norm_num : (0:ℝ)<20)] at hexp
  have hstrict : exp (cycleHarmonic m) < (110/3)*(m:ℝ)/20 :=
    hexp.trans_lt (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right exp_anchor hm0) (by norm_num))
  rw [exp_neg,←div_eq_mul_inv]
  apply (lt_div_iff₀ (exp_pos _)).mpr
  have hmk : (m:ℝ) < k := by exact_mod_cast (show m < k by dsimp [m]; omega)
  change 12/11 * exp (cycleHarmonic m) < _
  linarith only [hstrict,hmk]

#print axioms principal_harmonic_prefactor
end OpenMathResearch.LongCycleExcedances
