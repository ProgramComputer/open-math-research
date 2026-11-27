import FourierPoleDifferentiation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Filter MeasureTheory

/-- The angular L1 norm of the differentiated pole kernel is at most
2πR times the sum of its squared pole weights. -/
theorem complexPoleKernel_derivative_bound (P c : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i, ‖P i‖ ≠ R) (hfar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖)
    (hs : Summable fun i => poleWeight (c i) (P i) R)
    (hs2 : Summable fun i => squaredPoleWeight (c i) (P i) R) :
    (∫ x in (0:ℝ)..2*π, ‖deriv (complexPoleKernel P c R) x‖) ≤
      R*((∑' i, squaredPoleWeight (c i) (P i) R)*(2*π)) := by
  let b := fun i => squaredPoleWeight (c i) (P i) R
  let u := fun i x => b i*(normalizedPole (P i) R x)^2
  let g := fun i x => c i/(P i-circleMap 0 R x)^2
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform P hR hp hfar
  have hb i : 0 ≤ b i := div_nonneg (norm_nonneg _) (abs_nonneg _)
  have hn i x : 0 ≤ u i x := mul_nonneg (hb i) (sq_nonneg _)
  have hdom i x : u i x ≤ b i*M^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (normalizedPole_nonneg _ _ _) (hu i x) 2) (hb i)
  have hNorm i x : ‖g i x‖ = u i x := norm_squared_pole_term _ _ hR (hp i) x
  have hsum x : Summable (fun i => ‖g i x‖) := Summable.of_nonneg_of_le
    (fun i => norm_nonneg _) (fun i => (hNorm i x).le.trans (hdom i x)) (hs2.mul_right (M^2))
  have cg : Continuous (fun x => ∑' i, g i x) := by
    apply continuous_tsum _ (hs2.mul_right (M^2)) (fun i x => (hNorm i x).le.trans (hdom i x))
    intro i
    apply continuous_const.div ((continuous_const.sub (continuous_circleMap _ _)).pow 2)
    intro x
    exact pow_ne_zero _ (sub_ne_zero.mpr
      (fun he => hp i ((congrArg norm he).trans ((norm_circleMap_zero R x).trans (abs_of_pos hR)))))
  have cu : Continuous (fun x => ∑' i, u i x) := by
    apply continuous_tsum
      (fun i => continuous_const.mul ((normalizedPole_continuous hR (hp i)).pow 2)) (hs2.mul_right (M^2))
    intro i x
    exact (Real.norm_of_nonneg (hn i x)).le.trans (hdom i x)
  have hd (x) : ‖deriv (complexPoleKernel P c R) x‖ = R*‖∑' i, g i x‖ := by
    rw [(complexPoleKernel_angular_deriv P c hR hp hfar hs hs2 x).deriv]
    simp only [norm_mul,Complex.norm_I,one_mul,norm_circleMap_zero,abs_of_pos hR,g]
  simp_rw [hd]
  rw [intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hR.le
  apply le_trans _ (infinite_squared_pole_integral P b hR hp hfar hb hs2).le
  apply intervalIntegral.integral_mono_on Real.two_pi_pos.le (cg.norm.intervalIntegrable _ _)
    (cu.intervalIntegrable _ _)
  intro x _
  exact (norm_tsum_le_tsum_norm (hsum x)).trans_eq (tsum_congr (fun i => hNorm i x))

#print axioms complexPoleKernel_derivative_bound
end OpenMathResearch.LongCycleExcedances
