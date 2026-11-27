import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem nested_decay_at_size {q n k : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k) (hnq : n ≤ q) :
    ((1+1/(100*(k:ℝ)))⁻¹)^(q-1) ≤ exp (-(n:ℝ)/(200*(k:ℝ))) := by
  let K := (k:ℝ)
  have hK : 7 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hKp : 0 < K := by linarith
  have hN : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hq : (n:ℝ) ≤ q := by exact_mod_cast hnq
  have hqm : ((q-1:ℕ):ℝ)=(q:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one]
  let ρ := (1+1/(100*K))⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : ρ-1 = -1/(100*K+1) := by
    dsimp [ρ]
    field_simp <;> ring
  have hl := log_le_sub_one_of_pos hρ
  rw [he] at hl
  have hg : (n:ℝ)/(200*K) ≤ ((q:ℝ)-1)/(100*K+1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 200*K by positivity),
      mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) (show 0 ≤ 100*K-2 by linarith),hN]
  have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) (q-1))
  apply (log_le_log_iff (pow_pos hρ _) (exp_pos _)).mp
  change log (ρ^(q-1)) ≤ _
  rw [log_pow,log_exp]
  rw [hqm] at h ⊢
  change ((q:ℝ)-1)*log ρ ≤ -(n:ℝ)/(200*K)
  calc
    _ ≤ ((q:ℝ)-1)*(-1/(100*K+1)) := h
    _ = -(((q:ℝ)-1)/(100*K+1)) := by ring
    _ ≤ -((n:ℝ)/(200*K)) := neg_le_neg hg
    _ = _ := by ring

/-- Polynomial losses in the normalized row estimate are absorbed by the
same size condition as in the uniform interlacing argument. -/
theorem nested_size_envelope {q n k : ℕ} (hn : 100 ≤ n) (hk : 7 ≤ k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    400*(n:ℝ)^2 * exp (2*(6+9*log (k:ℝ))) * ((1+1/(100*(k:ℝ)))⁻¹)^(q-1)
      ≤ 1/(100*(n:ℝ)) := by
  have hn' : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hnp : (0:ℝ) < n := by linarith
  have hkp : (0:ℝ) < k := by linarith
  have hlog : log (k:ℝ) ≤ log (n:ℝ) := log_le_log hkp (by exact_mod_cast hkn)
  have hlogn : 1 ≤ log (n:ℝ) := (le_log_iff_exp_le hnp).mpr (by linarith only [Real.exp_one_lt_d9,hn'])
  have h2 : 2*(6+9*log (k:ℝ))-(n:ℝ)/(200*(k:ℝ)) ≤ -8-12*log (n:ℝ) := by linarith
  have h400 : (400:ℝ) ≤ exp 7 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤7 by norm_num) 7)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have h100 : (100:ℝ) ≤ exp 5 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ)≤5 by norm_num) 7)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have hA := nested_decay_at_size hn hk hnq
  apply (mul_le_mul_of_nonneg_left hA (by positivity)).trans
  rw [mul_assoc,←exp_add,neg_div,←sub_eq_add_neg]
  apply (mul_le_mul_of_nonneg_left (exp_le_exp.mpr h2) (by positivity)).trans
  rw [le_div_iff₀ (by positivity)]
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_right h400 (sq_nonneg (n:ℝ)))
    (mul_le_mul_of_nonneg_right h100 hnp.le) (by positivity : (0:ℝ) ≤ 100*n) (by positivity)
  have heqn : (n:ℝ)^2 = exp (2*log (n:ℝ)) := by rw [two_mul,exp_add,exp_log hnp,pow_two]
  have hnexp : (n:ℝ)=exp (log (n:ℝ)) := (exp_log hnp).symm
  have hpoly : 400*(n:ℝ)^2*(100*(n:ℝ)) ≤ exp (12+3*log (n:ℝ)) := by
    apply hmul.trans_eq
    nth_rw 1 [heqn]; nth_rw 2 [hnexp]
    rw [←exp_add,←exp_add,←exp_add]
    congr 1; ring
  have H := mul_le_mul_of_nonneg_right hpoly (exp_pos (-8-12*log (n:ℝ))).le
  rw [←exp_add] at H
  have htotal : exp (12+3*log (n:ℝ)+(-8-12*log (n:ℝ))) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith)
  linarith only [H,htotal,show 400*(n:ℝ)^2*exp (-8-12*log (n:ℝ))*(100*n)=400*(n:ℝ)^2*(100*n)*exp (-8-12*log (n:ℝ)) by ring]

#print axioms nested_decay_at_size
#print axioms nested_size_envelope
end OpenMathResearch.LongCycleExcedances
