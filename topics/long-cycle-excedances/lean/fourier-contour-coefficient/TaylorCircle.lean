import AnnularPrincipalParts
import Mathlib.Analysis.Analytic.OfScalars

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Set Metric Complex
open scoped Topology NNReal

/-- Identify the exact small-circle Cauchy coefficient with a convergent scalar
series. This allows the coefficient ID and the annular transfer to stay separate. -/
theorem taylor_circle_extract {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (closedBall 0 (ρ:ℝ)))
    (hs : ∀ᶠ w in 𝓝 (0:ℂ), HasSum (fun n => a n * w^n) (f w))
    (n : ℕ) :
    (∮ z in C((0:ℂ), (ρ:ℝ)), f z / z^(n+1)) =
      ((2:ℂ)*Real.pi*I) * a n := by
  let A := FormalMultilinearSeries.ofScalars ℂ a
  have ha : HasFPowerSeriesAt f A (0:ℂ) := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [hs] with z hz
    have hcoeff (n : ℕ) : A.coeff n = a n := by
      change (FormalMultilinearSeries.ofScalars ℂ a) n (fun _ => 1) = _
      rw [FormalMultilinearSeries.ofScalars_apply_eq]
      simp
    simpa only [hcoeff, zero_add, smul_eq_mul] using
      (show HasSum (fun n => z^n * a n) (f z) by simpa only [mul_comm (a _) _] using hz)
  have hc := (hf.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hρ
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1))
    (ha.eq_formalMultilinearSeries hc.hasFPowerSeriesAt)
  simp only [A, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    cauchyPowerSeries_apply, sub_zero, one_div] at he
  have hg (z : ℂ) : (z⁻¹)^n * (z⁻¹ * f z) = f z / z^(n+1) := by
    rw [div_eq_mul_inv, pow_succ, mul_inv_rev, inv_pow]
    ring
  simp only [mul_assoc, hg] at he
  have hne : (2:ℂ)*(Real.pi:ℂ)*I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [←mul_assoc (2:ℂ)] at he
  exact (eq_inv_mul_iff_mul_eq₀ hne).mp he |>.symm

#print axioms taylor_circle_extract
end OpenMathResearch.LongCycleExcedances
