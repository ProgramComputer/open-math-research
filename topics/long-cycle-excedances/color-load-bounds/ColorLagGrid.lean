import BinomialColorLoad
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- The residual color acceptance probability is at most one. This bounds
the original lag by one unweighted binomial grid at any positive rank. -/
theorem color_lag_grid_upper {n d p : ℕ} (hd : d ≤ n) (hp : 0 < p) (F : ℕ → ℝ) (L : ℝ)
    (hL : L ≤ (n.choose d:ℝ)*∑ j ∈ range (p+1), (j:ℝ)^d*F (p-j))
    (hF : ∀ i, F i ≤ (i:ℝ)^(n-d)) :
    L/(p:ℝ)^n ≤ ∑ j ∈ range (p+1), colorLoad n d ((j:ℝ)/p) := by
  have hpp : (0:ℝ) < p := by positivity
  have hpow : (p:ℝ)^d*(p:ℝ)^(n-d)=(p:ℝ)^n := by rw [←pow_add,Nat.add_sub_of_le hd]
  calc
    _ ≤ ((n.choose d:ℝ)*∑ j ∈ range (p+1), (j:ℝ)^d*F (p-j))/(p:ℝ)^n :=
      div_le_div_of_nonneg_right hL (by positivity)
    _ ≤ _ := by
      rw [mul_sum,sum_div]
      apply sum_le_sum
      intro j hj
      have hjp : j≤p := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hrest : 1-(j:ℝ)/p=((p-j:ℕ):ℝ)/p := by rw [Nat.cast_sub hjp,sub_div,div_self hpp.ne']
      have hh := mul_le_mul_of_nonneg_left (hF (p-j)) (by positivity : 0≤(j:ℝ)^d)
      have hi := mul_le_mul_of_nonneg_left hh (by positivity : 0≤(n.choose d:ℝ))
      apply (div_le_div_of_nonneg_right hi (by positivity : 0≤(p:ℝ)^n)).trans_eq
      unfold colorLoad
      rw [hrest,div_pow,div_pow,div_mul_div_comm,hpow]
      ring

#print axioms color_lag_grid_upper
end OpenMathResearch.LongCycleExcedances
