import FourWindowErrors

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Filter CycleProbability
open scoped Topology

/-- The two coefficient limits at adjacent sizes are sufficient. The real
normalization uses the same angular parameter on both rows. -/
theorem normalized_determinant_limit {k n : ℕ} (θ : ℝ) {old next : ℝ}
    (ho : Tendsto (fun A => finiteCoefficient A k (cos θ) (sin θ) n) atTop (𝓝 (old:ℂ)))
    (hn : Tendsto (fun A => finiteCoefficient A k (cos θ) (sin θ) (n+1)) atTop (𝓝 (next:ℂ))) :
    Tendsto (fun M => (k:ℝ)/sin θ*(windowDeterminant k n θ (symmetricPoleWindow M)).re) atTop
      (𝓝 ((k:ℝ)/sin θ*(sin ((n:ℝ)*θ+θ)*old-sin ((n:ℝ)*θ)*next))) := by
  let x := sin ((n:ℝ)*θ+θ)
  let y := sin ((n:ℝ)*θ)
  have h := ((ho.comp symmetric_pole_window_cofinal).const_mul (x:ℂ)).sub
    ((hn.comp symmetric_pole_window_cofinal).const_mul (y:ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  have hnorm := hr.const_mul ((k:ℝ)/sin θ)
  simpa only [Function.comp_apply,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,x,y,windowDeterminant] using hnorm

#print axioms normalized_determinant_limit
end OpenMathResearch.LongCycleExcedances
