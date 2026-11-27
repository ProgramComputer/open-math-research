import FourierPolePair

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory
open scoped BigOperators

/-- The squared-integral bound is bilinear in the two nonnegative pole weights.
The finite sets and their weights may differ. -/
theorem finite_pole_product_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (P : ι → ℂ) (Q : κ → ℂ) (a : ι → ℝ) (b : κ → ℝ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i ∈ s, ‖P i‖ ≠ R) (hq : ∀ j ∈ t, ‖Q j‖ ≠ R)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ t, 0 ≤ b j) :
    (∫ x in (0:ℝ)..2*π,
      (∑ i ∈ s, a i*normalizedPole (P i) R x)*(∑ j ∈ t, b j*normalizedPole (Q j) R x))
      ≤ (2*π)*(∑ i ∈ s, a i)*(∑ j ∈ t, b j) := by
  let terms := fun i j x => (a i*b j)*(normalizedPole (P i) R x*normalizedPole (Q j) R x)
  have hcont (i) (hi : i ∈ s) (j) (hj : j ∈ t) : Continuous (terms i j) :=
    continuous_const.mul ((normalizedPole_continuous hR (hp i hi)).mul
      (normalizedPole_continuous hR (hq j hj)))
  have bound (i) (hi : i ∈ s) (j) (hj : j ∈ t) :
      (∫ x in (0:ℝ)..2*π, terms i j x) ≤ a i*b j*(2*π) := by
    dsimp only [terms]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (normalizedPole_pair_integral hR (hp i hi) (hq j hj))
      (mul_nonneg (ha i hi) (hb j hj))
  calc
    _ = ∫ x in (0:ℝ)..2*π, ∑ i ∈ s, ∑ j ∈ t, terms i j x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [terms]
      ring
    _ = ∑ i ∈ s, ∑ j ∈ t, ∫ x in (0:ℝ)..2*π, terms i j x := by
      rw [intervalIntegral.integral_finset_sum (fun i hi =>
        (continuous_finset_sum _ (fun j hj => hcont i hi j hj)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro i hi
      exact intervalIntegral.integral_finset_sum (fun j hj => (hcont i hi j hj).intervalIntegrable _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, a i*b j*(2*π) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => bound i hi j hj))
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

#print axioms finite_pole_product_bound
end OpenMathResearch.LongCycleExcedances
