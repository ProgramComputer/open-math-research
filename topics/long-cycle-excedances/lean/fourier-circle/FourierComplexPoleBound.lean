import FourierInfinitePoleBound
import Mathlib.Analysis.NormedSpace.FunctionSeries

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory Filter

def poleWeight (c p : ℂ) (R : ℝ) : ℝ := ‖c‖ / √(poleGap p R)

def complexPoleKernel (P c : ℕ → ℂ) (R x : ℝ) : ℂ :=
  ∑' i, c i / (P i - circleMap 0 R x)

theorem norm_pole_term (c p : ℂ) {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) (x : ℝ) :
    ‖c/(p-circleMap 0 R x)‖ = poleWeight c p R * normalizedPole p R x := by
  rw [norm_div]
  unfold poleWeight normalizedPole
  field_simp [(Real.sqrt_pos.mpr (poleGap_pos hR hp)).ne']

private theorem rawPole_facts (P c : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, ‖P i‖ ≠ R) (hFar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖)
    (hs : Summable fun i => poleWeight (c i) (P i) R) :
    Continuous (complexPoleKernel P c R) ∧
    Continuous (fun x => ∑' i, poleWeight (c i) (P i) R * normalizedPole (P i) R x) ∧
    ∀ x, ‖complexPoleKernel P c R x‖ ≤ ∑' i, poleWeight (c i) (P i) R * normalizedPole (P i) R x := by
  let a := fun i => poleWeight (c i) (P i) R
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform P hR hg hFar
  have ha i : 0 ≤ a i := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb i x : a i * normalizedPole (P i) R x ≤ a i*M :=
    mul_le_mul_of_nonneg_left (hu i x) (ha i)
  have hn i x : 0 ≤ a i * normalizedPole (P i) R x :=
    mul_nonneg (ha i) (normalizedPole_nonneg _ _ _)
  have hc i : Continuous (fun x => c i/(P i-circleMap 0 R x)) := by
    apply continuous_const.div (continuous_const.sub (continuous_circleMap _ _))
    intro x
    exact sub_ne_zero.mpr (fun h => hg i ((congrArg norm h).trans ((norm_circleMap_zero R x).trans (abs_of_pos hR))))
  have hraw i x := (norm_pole_term (c i) (P i) hR (hg i) x).le.trans (hb i x)
  refine ⟨continuous_tsum hc (hs.mul_right M) hraw, ?_, ?_⟩
  · apply continuous_tsum (fun i => continuous_const.mul (normalizedPole_continuous hR (hg i))) (hs.mul_right M)
    intro i x
    rw [Real.norm_eq_abs,abs_of_nonneg (hn i x)]
    exact hb i x
  · intro x
    have hsum := Summable.of_nonneg_of_le (fun i => norm_nonneg (c i/(P i-circleMap 0 R x)))
      (fun i => hraw i x) (hs.mul_right M)
    exact (norm_tsum_le_tsum_norm hsum).trans_eq (tsum_congr (fun i => norm_pole_term _ _ hR (hg i) x))

/-- Angular L1 bound for the product of two arbitrary complex, countably infinite
pole sums. Both weights carry the exact L2 pole factor. -/
theorem complex_pole_product_bound (P Q c d : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i, ‖P i‖ ≠ R) (hq : ∀ j, ‖Q j‖ ≠ R)
    (hpFar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖) (hqFar : ∀ᶠ j in atTop, 2*R ≤ ‖Q j‖)
    (hs : Summable fun i => poleWeight (c i) (P i) R)
    (ht : Summable fun j => poleWeight (d j) (Q j) R) :
    (∫ x in (0:ℝ)..2*π, ‖complexPoleKernel P c R x * complexPoleKernel Q d R x‖) ≤
      (2*π)*(∑' i, poleWeight (c i) (P i) R)*(∑' j, poleWeight (d j) (Q j) R) := by
  obtain ⟨cp,cu,hu⟩ := rawPole_facts P c hR hp hpFar hs
  obtain ⟨cq,cv,hv⟩ := rawPole_facts Q d hR hq hqFar ht
  apply le_trans _ (infinite_pole_product_bound P Q _ _ hR hp hq hpFar hqFar
    (fun i => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (fun j => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hs ht)
  apply intervalIntegral.integral_mono_on Real.two_pi_pos.le ((cp.mul cq).norm.intervalIntegrable _ _)
    ((cu.mul cv).intervalIntegrable _ _)
  intro x _
  rw [norm_mul]
  exact mul_le_mul (hu x) (hv x) (norm_nonneg _) ((norm_nonneg _).trans (hu x))

#print axioms norm_pole_term
#print axioms complex_pole_product_bound
end OpenMathResearch.LongCycleExcedances
