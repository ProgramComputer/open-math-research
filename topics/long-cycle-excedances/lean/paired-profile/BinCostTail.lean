import CenteredBinGeometry
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset Real CycleProbability

theorem centeredErrorBound_le (j : ℕ) : centeredErrorBound j ≤ 4/7 := by
  unfold centeredErrorBound
  split
  · rfl
  split
  · norm_num
  apply le_trans (min_le_left ..)
  split <;> norm_num

/-- Split the sum over every bin into the checked integer head and a tail
controlled by evaluating the entire nonnegative polynomial at a tilt base. -/
theorem cost_split_head_tail (p : ℝ[X]) (M J : ℕ) (hdeg : p.natDegree ≤ M) (e v : ℕ→ℝ) {H base : ℝ}
    (hbase : 1 ≤ base) (hH : 0 ≤ H)
    (hp : ∀ b, 0 ≤ p.coeff b) (hv : ∀ b, 0 ≤ v b)
    (he : ∀ b, 0 ≤ e b ∧ e b ≤ H) (hhead : ∀ b ≤ J, p.coeff b ≤ v b) :
    (∑ b ∈ range (M+1), e b*p.coeff b) ≤
      (∑ b ∈ range (J+1), e b*v b)+H/base^J*p.eval base := by
  let D := range (M+1)
  let head := fun b => if b ≤ J then e b*v b else 0
  have hbp : 0 < base^J := pow_pos (by linarith) J
  have hbin (b : ℕ) : e b*p.coeff b ≤ head b + H/base^J*(p.coeff b*base^b) := by
    by_cases hb : b ≤ J
    · rw [show head b=e b*v b by simp [head,hb]]
      exact (mul_le_mul_of_nonneg_left (hhead b hb) (he b).1).trans
        (le_add_of_nonneg_right (mul_nonneg (div_nonneg hH hbp.le) (mul_nonneg (hp b) (pow_nonneg (by linarith) _))))
    · rw [show head b=0 by simp [head,hb],zero_add]
      have hpow := pow_le_pow_right₀ hbase (le_of_not_ge hb)
      have hscaled : H ≤ H/base^J*base^b := by
        calc
          H = H/base^J*base^J := (div_mul_cancel₀ _ hbp.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      calc
        _ ≤ (H/base^J*base^b)*p.coeff b := mul_le_mul_of_nonneg_right ((he b).2.trans hscaled) (hp b)
        _ = _ := by ring
  have hh : (∑ b ∈ D, head b) ≤ ∑ b ∈ range (J+1), e b*v b := by
    rw [show (∑ b ∈ D, head b)=∑ b ∈ D.filter (· ≤ J), e b*v b by rw [sum_filter]]
    apply sum_le_sum_of_subset_of_nonneg
    · intro b hb
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hb).2)
    · intro b _ _
      exact mul_nonneg (he b).1 (hv b)
  have hf := sum_le_sum (s:=D) (fun b _ => hbin b)
  rw [sum_add_distrib,←mul_sum] at hf
  apply hf.trans (add_le_add hh _)
  exact le_of_eq (by rw [eval_eq_sum_range' (n:=M+1) (Nat.lt_succ_of_le hdeg)])

theorem product_tilt_cost_bound {ι : Type*} (A : Finset ι) (p : ι → ℝ[X])
    (base T : ℝ) (hp : ∀ q ∈ A, 0 ≤ (p q).eval base)
    (hT : (∑ q ∈ A, (p q).eval base) ≤ T) :
    (binFull A p).eval base ≤ exp T := by
  rw [binFull,eval_prod]
  apply le_trans _ (exp_le_exp.mpr hT)
  rw [exp_sum]
  apply prod_le_prod
  · intro q hq
    simp only [eval_add,eval_one]
    linarith only [hp q hq]
  · intro q _
    simp only [eval_add,eval_one]
    linarith only [add_one_le_exp ((p q).eval base)]

/-- Exact reserve assigned to the discarded bins in the two principal terms. -/
theorem symmetric_bin_tail_reserve :
    2*(4/7:ℝ)/(9/8:ℝ)^240*exp 14 < 1/10000 := by
  have h1 : exp 1 < (11/4:ℝ) := by linarith only [Real.exp_one_lt_d9]
  have he : exp (14:ℝ) < (11/4:ℝ)^14 := by
    have hp := pow_lt_pow_left₀ h1 (exp_pos _).le (by decide : (14:ℕ)≠0)
    rwa [←Real.exp_nat_mul, mul_one] at hp
  have hq : 2*(4/7:ℝ)/(9/8:ℝ)^240*(11/4:ℝ)^14 < 1/10000 := by norm_num
  exact (mul_lt_mul_of_pos_left he (by positivity : 0 < 2*(4/7:ℝ)/(9/8:ℝ)^240)).trans hq

#print axioms cost_split_head_tail
#print axioms product_tilt_cost_bound
#print axioms symmetric_bin_tail_reserve
end OpenMathResearch.LongCycleExcedances
