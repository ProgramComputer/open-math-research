import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The adaptive exterior cap lies below one half. The rank condition
is supplied by the floor geometry, independently of the phase join. -/
theorem front_cap_lt_half {n : ℕ} {H : ℝ} (hn : 10000 ≤ n) (hH : 0 < H)
    (hbudget : (H+1)^2 ≤ (9/25:ℝ)^2*n) :
    (459/40:ℝ)*(H/(H+1))^n < 1/2 := by
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hh : 0 < H+1 := by linarith
  have hs : H+1 ≤ (n:ℝ)/25 := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [hbudget, mul_nonneg (sub_nonneg.mpr hn') hn₀]
  have hdiv : (25:ℝ) ≤ (n:ℝ)/(H+1) := by
    apply (le_div_iff₀ hh).2
    linarith only [hs]
  have hmod : 0 < H/(H+1) := div_pos hH hh
  have hlog : log (H/(H+1)) = -log (1+1/H) := by
    rw [←Real.log_inv]
    congr 1
    field_simp [hH.ne',hh.ne'] <;> ring
  have hlog₁ : 1/(H+1) ≤ log (1+1/H) := by
    have h := Real.le_log_one_add_of_nonneg (x := 1/H) (by positivity)
    have he : 2*(1/H)/(1/H+2) = 1/(H+1/2) := by
      field_simp [hH.ne'] <;> ring
    rw [he] at h
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans h
  have hlog₂ := mul_le_mul_of_nonneg_left hlog₁ hn₀
  rw [mul_one_div] at hlog₂
  have hpow : (H/(H+1))^n ≤ exp (-((n:ℝ)/(H+1))) := by
    apply (log_le_log_iff (pow_pos hmod _) (exp_pos _)).mp
    rw [log_pow,log_exp,hlog]
    linarith only [hlog₂]
  have hexp : (459/20:ℝ) < exp ((n:ℝ)/(H+1)) := by
    linarith only [Real.add_one_le_exp ((n:ℝ)/(H+1)),hdiv]
  have hf : (459/40:ℝ)*exp (-((n:ℝ)/(H+1))) < 1/2 := by
    rw [exp_neg,←div_eq_mul_inv,div_lt_iff₀ (exp_pos _)]
    linarith only [hexp]
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_lt hf

theorem front_lag_cutoff_gap {n h : ℕ} (hn : 10000 ≤ n)
    (hh : h ≤ ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊) :
    h+2 ≤ ⌊sqrt (n:ℝ)/2⌋₊ := by
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 100 ≤ sqrt (n:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).2 (by norm_num; exact hn)
  have hh' : (h:ℝ) ≤ (7/20:ℝ)*sqrt (n:ℝ) :=
    (show (h:ℝ) ≤ ((⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊:ℕ):ℝ) by exact_mod_cast hh).trans
      (Nat.floor_le (by positivity))
  apply (Nat.le_floor_iff' (by omega)).2
  push_cast
  linarith only [hs,hh']

#print axioms front_lag_cutoff_gap
#print axioms front_cap_lt_half
end OpenMathResearch.LongCycleExcedances
