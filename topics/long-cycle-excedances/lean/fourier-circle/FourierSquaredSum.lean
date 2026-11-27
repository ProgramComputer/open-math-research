import FourierInfinitePoleBound

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory Filter

/-- Squared poles retain an exact angular mass for every nonnegative summable
coefficient sequence. This is the positive majorant of a differentiated pole sum. -/
theorem infinite_squared_pole_integral (P : ℕ → ℂ) (a : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i, ‖P i‖ ≠ R) (hfar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    (∫ x in (0:ℝ)..2*π, ∑' i, a i*(normalizedPole (P i) R x)^2) = (∑' i, a i)*(2*π) := by
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform P hR hp hfar
  let F := fun i x => a i*(normalizedPole (P i) R x)^2
  have cf (i) : Continuous (F i) := continuous_const.mul ((normalizedPole_continuous hR (hp i)).pow 2)
  have nn (i) x : 0 ≤ F i x := mul_nonneg (ha i) (sq_nonneg _)
  have hdom i x : F i x ≤ a i*M^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (normalizedPole_nonneg _ _ _) (hu i x) 2) (ha i)
  have hsum (x : ℝ) : Summable (fun i => F i x) :=
    Summable.of_nonneg_of_le (fun i => nn i x) (fun i => hdom i x) (hs.mul_right (M^2))
  have hraw := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ:=volume) (a:=0) (b:=2*π) (F:=F) (fun i _ => a i*M^2)
    (fun i => (cf i).aestronglyMeasurable)
    (fun i => ae_of_all _ (fun x _ => by rw [Real.norm_eq_abs,abs_of_nonneg (nn i x)]; exact hdom i x))
    (ae_of_all _ (fun _ _ => hs.mul_right (M^2))) intervalIntegrable_const
    (ae_of_all _ (fun x _ => (hsum x).hasSum))
  have he (i) : (∫ x in (0:ℝ)..2*π, F i x) = a i*(2*π) := by
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul,normalizedPole_second_moment hR (hp i)]
  simpa only [he,tsum_mul_right] using hraw.tsum_eq.symm

#print axioms infinite_squared_pole_integral
end OpenMathResearch.LongCycleExcedances
