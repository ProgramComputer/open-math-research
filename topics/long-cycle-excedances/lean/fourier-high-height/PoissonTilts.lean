import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem expTerms_le {x : ℝ} (hx : 0 ≤ x) (F : Finset ℕ) :
    (∑ i ∈ F, x^i / (i.factorial : ℝ)) ≤ exp x := by
  let N := F.sup id + 1
  have hsub : F ⊆ range N := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hi))
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)).trans
    (sum_le_exp_of_nonneg hx N)

theorem poisson_lower_tilt {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hm : (5/4:ℝ)*k ≤ x) :
    (∑ i ∈ range (k-1), x^i / (i.factorial : ℝ)) ≤ exp (49/50*x) := by
  have he : (5/4:ℝ) ≤ exp (9/40) := by
    calc
      _ ≤ 1+(9/40:ℝ)+(9/40:ℝ)^2/2 := by norm_num
      _ ≤ _ := quadratic_le_exp_of_nonneg (by norm_num)
  calc
    _ ≤ ∑ i ∈ range (k-1), exp (k*(9/40)) * ((4/5*x)^i / (i.factorial:ℝ)) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      have hp : (5/4:ℝ)^i ≤ exp (k*(9/40)) := by
        rw [exp_nat_mul]
        exact (pow_le_pow_left₀ (by norm_num) he _).trans
          (pow_le_pow_right₀ (by linarith) hik)
      have hpos : 0 ≤ (4/5*x)^i / (i.factorial:ℝ) := by positivity
      calc
        _ = (5/4:ℝ)^i * ((4/5*x)^i / (i.factorial:ℝ)) := by
          rw [← mul_div_assoc, ← mul_pow, show (5/4:ℝ)*(4/5*x)=x by ring]
        _ ≤ _ := mul_le_mul_of_nonneg_right hp hpos
    _ = exp (k*(9/40)) * ∑ i ∈ range (k-1), (4/5*x)^i / (i.factorial:ℝ) := by
      rw [mul_sum]
    _ ≤ exp (k*(9/40)) * exp (4/5*x) :=
      mul_le_mul_of_nonneg_left (expTerms_le (by positivity) _) (exp_pos _).le
    _ ≤ _ := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      linarith

theorem poisson_upper_tilt {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (F : Finset ℕ)
    (hF : ∀ i ∈ F, k ≤ i) :
    (∑ i ∈ F, x^i / (i.factorial : ℝ)) ≤ exp (2*x-(2/3:ℝ)*k) := by
  have he : (2/3:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hp : exp ((2/3:ℝ)*k) ≤ (2:ℝ)^k := by
    rw [mul_comm (2/3:ℝ), exp_nat_mul]
    apply pow_le_pow_left₀ (exp_pos _).le
    exact (exp_le_exp.mpr he).trans (le_of_eq (exp_log (by norm_num)))
  calc
    _ ≤ ∑ i ∈ F, (exp (-(2/3:ℝ)*k)) * ((2*x)^i / (i.factorial:ℝ)) := by
      apply sum_le_sum
      intro i hi
      have hpi : exp ((2/3:ℝ)*k) ≤ (2:ℝ)^i :=
        hp.trans (pow_le_pow_right₀ (by norm_num) (hF i hi))
      rw [show -(2/3:ℝ)*k = -((2/3:ℝ)*k) by ring, exp_neg]
      apply (le_inv_mul_iff₀ (exp_pos _)).mpr
      rw [← mul_div_assoc, mul_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hpi (by positivity)
    _ = exp (-(2/3:ℝ)*k) * ∑ i ∈ F, (2*x)^i / (i.factorial:ℝ) := by rw [mul_sum]
    _ ≤ exp (-(2/3:ℝ)*k) * exp (2*x) :=
      mul_le_mul_of_nonneg_left (expTerms_le (by positivity) _) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

#print axioms poisson_lower_tilt
#print axioms poisson_upper_tilt
end OpenMathResearch.LongCycleExcedances
