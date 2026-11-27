import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

namespace OpenMathResearch.LongCycleExcedances

open scoped BigOperators Real

/-- The positive half of the shifted Cauchy lattice is bounded by its
decreasing integral, with the endpoint dropped. -/
theorem cauchy_lattice_prefix {B : ℝ} (hB : 0 < B) (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 + (B * (i + 1 : ℕ)) ^ 2)⁻¹) ≤ π / (2 * B) := by
  let F : ℝ → ℝ := fun t => (1 + (B * t)^2)⁻¹
  have hanti : AntitoneOn F (Set.Icc (0 : ℝ) (0 + N)) := by
    intro x hx y _ hy
    have hx0 : 0 ≤ x := hx.1
    dsimp only [F]
    have hnon : 0 ≤ B * x := mul_nonneg hB.le hx0
    have hmul : B * x ≤ B * y := mul_le_mul_of_nonneg_left hy hB.le
    have hsq := pow_le_pow_left₀ hnon hmul 2
    apply inv_anti₀ (by positivity)
    linarith
  have hchange : B * (∫ x in (0:ℝ)..(N:ℝ), F x) = Real.arctan (B * N) := by
    dsimp only [F]
    rw [intervalIntegral.mul_integral_comp_mul_left (f := fun x : ℝ => (1 + x^2)⁻¹) B]
    rw [mul_zero, integral_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have hsum := hanti.sum_le_integral
  simp only [zero_add] at hsum
  calc
    _ ≤ ∫ x in (0:ℝ)..(N:ℝ), F x := hsum
    _ ≤ π / (2 * B) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith only [hchange, Real.arctan_lt_pi_div_two (B * N)]

/-- The paired odd-pole moment bound for powers of degree at least two.
The positive index i represents odd poles +(2i+3) and -(2i+3). -/
theorem normalized_pole_moment_prefix {S : ℝ} (hS : 0 < S)
    {j : ℕ} (hj : 2 ≤ j) (N : ℕ) :
    2 + 2 * (∑ i ∈ Finset.range N,
      (1 + 4 * ((i+1:ℕ):ℝ) * (i+2:ℕ) * S^2) ^ (-(j:ℝ)/2)) ≤
      2 + 9 / (4 * S * Real.sqrt j) := by
  let B := S * Real.sqrt (2 * (j:ℝ))
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hB : 0 < B := by dsimp [B]; positivity
  have hterm (i : ℕ) :
      (1 + 4 * ((i+1:ℕ):ℝ) * (i+2:ℕ) * S^2) ^ (-(j:ℝ)/2) ≤
        (1 + (B * (i + 1 : ℕ)) ^ 2)⁻¹ := by
    let x : ℝ := 4 * ((i+1:ℕ):ℝ) * (i+2:ℕ) * S^2
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hbase : 0 < 1 + x := by linarith
    have hBern := one_add_mul_self_le_rpow_one_add (s:=x) (p:=(j:ℝ)/2)
      (by linarith) (by linarith)
    have hsum :
        1 + (B * (i + 1 : ℕ)) ^ 2 ≤ 1 + (j:ℝ)/2 * x := by
      have hs := Real.sq_sqrt (show 0 ≤ 2 * (j:ℝ) by positivity)
      have heq : B^2 = S^2 * (2 * (j:ℝ)) := by rw [show B = S * _ by rfl, mul_pow, hs]
      rw [mul_pow, heq]
      have hx' : (i:ℝ) + 1 ≤ (i:ℝ) + 2 := by linarith
      have hprod := mul_le_mul_of_nonneg_left hx'
        (show 0 ≤ 2 * (j:ℝ) * ((i:ℝ)+1) * S^2 by positivity)
      dsimp only [x]
      push_cast
      nlinarith only [hprod]
    change (1+x) ^ (-(j:ℝ)/2) ≤ _
    rw [neg_div, Real.rpow_neg hbase.le]
    exact inv_anti₀ (by positivity) (hsum.trans hBern)
  have hsum := (Finset.sum_le_sum (fun i _ => hterm i)).trans (cauchy_lattice_prefix hB N)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot2 : (7/5:ℝ) < Real.sqrt 2 := by
    nlinarith only [hsq2, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 7/5)]
  have hpi : π ≤ 9/4 * Real.sqrt 2 := by
    have hp := Real.pi_lt_d2
    linarith
  have hsJ : 0 < Real.sqrt (j:ℝ) := by positivity
  have hcost : π / (2 * B) ≤ 9 / (8 * S * Real.sqrt (j:ℝ)) := by
    rw [show B = S * (Real.sqrt 2 * Real.sqrt (j:ℝ)) by
      unfold B
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h := mul_le_mul_of_nonneg_right hpi
      (show 0 ≤ 8 * S * Real.sqrt (j:ℝ) by positivity)
    linarith only [h]
  have hdouble : 2 * (9 / (8 * S * Real.sqrt (j:ℝ))) = 9 / (4 * S * Real.sqrt (j:ℝ)) := by ring
  rw [← hdouble]
  linarith only [hsum.trans hcost]

/-- The infinite paired nonprincipal pole moment converges with the same
bound. The explicit two principal poles each contribute one. -/
theorem normalized_pole_moment {S : ℝ} (hS : 0 < S) {j : ℕ} (hj : 2 ≤ j) :
    let f : ℕ → ℝ := fun i =>
      (1 + 4 * ((i+1:ℕ):ℝ) * (i+2:ℕ) * S^2) ^ (-(j:ℝ)/2)
    Summable f ∧ 2 + 2 * (∑' i, f i) ≤ 2 + 9 / (4 * S * Real.sqrt j) := by
  dsimp only
  let f : ℕ → ℝ := fun i =>
      (1 + 4 * ((i+1:ℕ):ℝ) * (i+2:ℕ) * S^2) ^ (-(j:ℝ)/2)
  have hnon (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  have hprefix (N : ℕ) : ∑ i ∈ Finset.range N, f i ≤ (9 / (4*S*Real.sqrt j)) / 2 := by
    have h := normalized_pole_moment_prefix hS hj N
    change 2 + 2 * (∑ i ∈ Finset.range N, f i) ≤ _ at h
    linarith only [h]
  refine ⟨summable_of_sum_range_le hnon hprefix, ?_⟩
  have h := Real.tsum_le_of_sum_range_le hnon hprefix
  change 2 + 2 * (∑' i, f i) ≤ _
  linarith only [h]

#print axioms normalized_pole_moment
#print axioms cauchy_lattice_prefix
#print axioms normalized_pole_moment_prefix

end OpenMathResearch.LongCycleExcedances
