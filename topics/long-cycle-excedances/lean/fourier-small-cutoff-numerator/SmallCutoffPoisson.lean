import PoissonTilts

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

/-- The Chernoff lower-tail prefix allows different rational split points
without changing the underlying exponential-frequency representation. -/
theorem poisson_lower_tilt_at {x u l : ℝ} (hx : 0 ≤ x) (hu : 1 ≤ u)
    (hl : 0 ≤ l) (hexp : u ≤ exp l) (k : ℕ) (hm : u*k ≤ x) :
    (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp (((1+l)/u)*x) := by
  have hu0 : 0 < u := by linarith
  calc
    _ ≤ ∑ i ∈ range (k-1), exp (k*l) * ((x/u)^i/(i.factorial:ℝ)) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      have hp : u^i ≤ exp (k*l) := by
        rw [exp_nat_mul]
        have hb : 1 ≤ exp l := Real.one_le_exp_iff.mpr hl
        have h := pow_le_pow_right₀ hb hik
        exact (pow_le_pow_left₀ hu0.le hexp i).trans h
      have hpos : 0 ≤ (x/u)^i/(i.factorial:ℝ) := by positivity
      calc
        _ = u^i*((x/u)^i/(i.factorial:ℝ)) := by
          rw [← mul_div_assoc, ←mul_pow, show u*(x/u)=x by field_simp [hu0.ne'] <;> ring]
        _ ≤ _ := mul_le_mul_of_nonneg_right hp hpos
    _ = exp (k*l) * ∑ i ∈ range (k-1), (x/u)^i/(i.factorial:ℝ) := by rw [mul_sum]
    _ ≤ exp (k*l)*exp (x/u) :=
      mul_le_mul_of_nonneg_left (expTerms_le (by positivity) _) (exp_pos _).le
    _ ≤ _ := by
      rw [←exp_add]
      apply exp_le_exp.mpr
      have hy : (k:ℝ) ≤ x/u := (le_div_iff₀ hu0).mpr (by simpa [mul_comm] using hm)
      nlinarith only [mul_le_mul_of_nonneg_right hy hl, show (1+l)/u*x = (1+l)*(x/u) by ring]

theorem poisson_prefix_fifty {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hm : (7/5:ℝ)*k ≤ x) :
    (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((191/200)*x) := by
  have hE : (7/5:ℝ) ≤ exp (337/1000) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 337/1000 by norm_num) 4)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  convert poisson_lower_tilt_at hx (show (1:ℝ) ≤ 7/5 by norm_num)
    (show (0:ℝ) ≤ 337/1000 by norm_num) hE k hm using 1 <;> norm_num

theorem poisson_prefix_ten {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hm : (2:ℝ)*k ≤ x) :
    (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((7/8)*x) := by
  have hE : (2:ℝ) ≤ exp (3/4) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/4 by norm_num) 4)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  convert poisson_lower_tilt_at hx (show (1:ℝ) ≤ 2 by norm_num)
    (show (0:ℝ) ≤ 3/4 by norm_num) hE k hm using 1 <;> norm_num

#print axioms poisson_lower_tilt_at
#print axioms poisson_prefix_fifty
#print axioms poisson_prefix_ten
end OpenMathResearch.LongCycleExcedances
