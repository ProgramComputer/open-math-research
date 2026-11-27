import FourierLatticeDerivative

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Filter
open scoped Topology

/-- Angular derivative factor for an odd-indexed pole kernel. -/
def oddKernelSlope (P d : ℤ → ℂ) (R x : ℝ) : ℂ :=
  circleMap 0 R x * ∑' l, d l / (P l - circleMap 0 R x)^2

set_option maxHeartbeats 1500000 in
theorem odd_kernel_calculus (P d : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) (hs : Summable fun l => poleWeight (d l) (P l) R) :
    Continuous (oddKernelSlope P d R) ∧
      ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∑' l, d l / (P l-circleMap 0 R y))
        (I*oddKernelSlope P d R x) x := by
  let e := Equiv.intEquivNat.symm
  have he : Tendsto e atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact e.injective.tendsto_cofinite
  have hfar := he.eventually (lattice_eventually_far P hP hR)
  have ht := lattice_squared_weights P d hP hR hs
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform (P ∘ e) hR (fun i => hg _) hfar
  constructor
  · unfold oddKernelSlope
    apply (continuous_circleMap _ _).mul
    have heq : (fun x : ℝ => ∑' l, d l/(P l-circleMap 0 R x)^2) =
        (fun x : ℝ => ∑' i, d (e i)/(P (e i)-circleMap 0 R x)^2) := by
      funext x
      exact (e.tsum_eq _).symm
    rw [heq]
    refine continuous_tsum (u := fun i => squaredPoleWeight (d (e i)) (P (e i)) R * M^2)
      ?_ ((e.summable_iff.mpr ht).mul_right _) ?_
    · intro i
      apply continuous_const.div
        ((continuous_const.sub (continuous_circleMap _ _)).pow _)
      intro x
      apply pow_ne_zero
      apply sub_ne_zero.mpr
      exact fun eq => hg (e i) ((congrArg norm eq).trans
        ((norm_circleMap_zero R x).trans (abs_of_pos hR)))
    · intro i x
      rw [norm_squared_pole_term _ _ hR (hg (e i))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (normalizedPole_nonneg _ _ _) (hu i x) 2)
        (div_nonneg (norm_nonneg _) (abs_nonneg _))
  · intro x
    have h := complexPoleKernel_angular_deriv (P ∘ e) (d ∘ e) hR
      (fun i => hg _) hfar (e.summable_iff.mpr hs) (e.summable_iff.mpr ht) x
    have hfun : complexPoleKernel (P ∘ e) (d ∘ e) R =
        fun y : ℝ => ∑' l, d l/(P l-circleMap 0 R y) := by
      funext y
      exact e.tsum_eq (fun l => d l/(P l-circleMap 0 R y))
    rw [hfun] at h
    unfold oddKernelSlope
    exact h.congr_deriv (by rw [← e.tsum_eq (fun l => d l/(P l-circleMap 0 R x)^2)]; rfl)

#print axioms odd_kernel_calculus
end OpenMathResearch.LongCycleExcedances
