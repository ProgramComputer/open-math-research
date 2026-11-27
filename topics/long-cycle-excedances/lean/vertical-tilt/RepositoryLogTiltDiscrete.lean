import ComplexDiscreteMoment
import MonomialTiltBounds
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances

/-- The coefficients of the actual finite log tilt have the complex discrete
moment representation on the positive logarithmic half-axis. -/
theorem cutoffLogCoefficient_hasSum {k d : ℕ} (hd : 1 ≤ d) (hdk : d < k)
    {x : ℝ} (hx : 0 < x) :
    HasSum (fun i : ℕ => ((-Real.exp (-x):ℝ):ℂ)^(i+1) * (((i+1:ℕ):ℂ)^(d-1)))
      (-((cutoffLogCoefficient k (-Real.exp (-x)) d : ℂ)) * (d.factorial:ℂ)) := by
  by_cases hone : d = 1
  · subst d
    have hnorm : ‖((-Real.exp (-x):ℝ):ℂ)‖ < 1 := by
      simpa only [Complex.norm_real] using norm_negative_exp_lt_one hx
    have h := shifted_complex_geometric hnorm
    simpa [cutoffLogCoefficient, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_neg,
      neg_div] using h
  · have hd₂ : 2 ≤ d := by omega
    let t : ℝ := -Real.exp (-x)
    have hcoeff : -((cutoffLogCoefficient k t d : ℂ)) * (d.factorial:ℂ) =
        (LongCycleBounds.Band.moment d t : ℂ) := by
      rw [cutoffLogCoefficient, if_neg hone, if_pos ⟨hd₂,hdk⟩,
        Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast, neg_div, neg_neg]
      exact div_mul_cancel₀ _ (by exact_mod_cast d.factorial_ne_zero)
    rw [hcoeff]
    exact complex_hasSum_discrete_moment hx hd₂ (LongCycleBounds.Band.moment_discrete d hd₂ x hx)

theorem coherentPole_exp_neg (x : ℝ) (l : ℤ) :
    Complex.exp (-(coherentPole x l)) = ((-Real.exp (-x):ℝ):ℂ) := by
  simpa only [coherentPole] using complex_exp_negative_odd_pole x l

#print axioms cutoffLogCoefficient_hasSum
#print axioms coherentPole_exp_neg
end RepositoryQuotientAudit
