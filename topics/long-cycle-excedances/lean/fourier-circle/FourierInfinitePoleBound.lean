import FourierFinitePoleBound
import FourierPoleUniform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory Filter
open scoped Topology

private def prefixKernel (P : ℕ → ℂ) (a : ℕ → ℝ) (R : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, a i*normalizedPole (P i) R x

private theorem prefixKernel_nonneg {P : ℕ → ℂ} {a : ℕ → ℝ} {R : ℝ} (ha : ∀ i, 0 ≤ a i)
    (n : ℕ) (x : ℝ) : 0 ≤ prefixKernel P a R n x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (normalizedPole_nonneg _ _ _))

private theorem prefixKernel_bound {P : ℕ → ℂ} {a : ℕ → ℝ} {R M : ℝ} (ha : ∀ i, 0 ≤ a i)
    (has : Summable a) (hM : 0 ≤ M) (hu : ∀ i x, normalizedPole (P i) R x ≤ M)
    (n : ℕ) (x : ℝ) : prefixKernel P a R n x ≤ (∑' i, a i)*M := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, a i*M :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hu i x) (ha i))
    _ = (∑ i ∈ Finset.range n, a i)*M := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (has.sum_le_tsum _ (fun i _ => ha i)) hM

private theorem prefixKernel_limit {P : ℕ → ℂ} {a : ℕ → ℝ} {R M : ℝ} (ha : ∀ i, 0 ≤ a i)
    (has : Summable a) (hu : ∀ i x, normalizedPole (P i) R x ≤ M) (x : ℝ) :
    Tendsto (fun n => prefixKernel P a R n x) atTop (𝓝 (∑' i, a i*normalizedPole (P i) R x)) := by
  have hsum := Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (normalizedPole_nonneg (P i) R x))
    (fun i => mul_le_mul_of_nonneg_left (hu i x) (ha i)) (has.mul_right M)
  exact hsum.hasSum.tendsto_sum_nat

/-- Countably many poles may be used on both lists. Each avoids the circle, and only
finitely many on each list have modulus below twice the radius. The angular bound
depends only on the two total weights. -/
theorem infinite_pole_product_bound (P Q : ℕ → ℂ) (a b : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i, ‖P i‖ ≠ R) (hq : ∀ j, ‖Q j‖ ≠ R)
    (hpFar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖) (hqFar : ∀ᶠ j in atTop, 2*R ≤ ‖Q j‖)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (has : Summable a) (hbs : Summable b) :
    (∫ x in (0:ℝ)..2*π,
      (∑' i, a i*normalizedPole (P i) R x)*(∑' j, b j*normalizedPole (Q j) R x))
      ≤ (2*π)*(∑' i, a i)*(∑' j, b j) := by
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform P hR hp hpFar
  obtain ⟨N,hN,hv⟩ := normalizedPole_uniform Q hR hq hqFar
  let F := fun n x => prefixKernel P a R n x * prefixKernel Q b R n x
  have hf (n) : Continuous (F n) := by
    apply Continuous.mul
    · exact continuous_finset_sum _ (fun i _ => continuous_const.mul (normalizedPole_continuous hR (hp i)))
    · exact continuous_finset_sum _ (fun j _ => continuous_const.mul (normalizedPole_continuous hR (hq j)))
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2*π) (F := F) (l := atTop)
    (fun _ => ((∑' i, a i)*M)*((∑' j, b j)*N))
    (Eventually.of_forall (fun n => (hf n).aestronglyMeasurable))
    (Eventually.of_forall (fun n => ae_of_all _ (fun x _ => by
      have hu0 := prefixKernel_nonneg (P := P) (R := R) ha n x
      have hv0 := prefixKernel_nonneg (P := Q) (R := R) hb n x
      have hu1 := prefixKernel_bound ha has hM hu n x
      have hv1 := prefixKernel_bound hb hbs hN hv n x
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hu0 hv0)]
      exact mul_le_mul hu1 hv1 hv0 (hu0.trans hu1))))
    intervalIntegrable_const
    (ae_of_all _ (fun x _ => (prefixKernel_limit ha has hu x).mul (prefixKernel_limit hb hbs hv x)))
  apply le_of_tendsto_of_tendsto' hlim
    ((tendsto_const_nhds.mul has.hasSum.tendsto_sum_nat).mul hbs.hasSum.tendsto_sum_nat)
  intro n
  exact finite_pole_product_bound _ _ P Q a b hR (fun i _ => hp i) (fun j _ => hq j)
    (fun i _ => ha i) (fun j _ => hb j)

#print axioms infinite_pole_product_bound
end OpenMathResearch.LongCycleExcedances
