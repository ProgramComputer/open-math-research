import FourierRealContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Set

/-- A direct characterization of singularities of the logistic denominator. -/
theorem logistic_denominator_zero_iff (s : ℝ) (w : ℂ) :
    1+Complex.exp (w-(s:ℂ))=0 ↔
      w ∈ Set.range (fun l : ℤ => (s:ℂ)+(2*(l:ℂ)+1)*π*I) := by
  have hpi := Complex.exp_pi_mul_I
  constructor
  · intro h
    have he : Complex.exp (w-(s:ℂ)) = Complex.exp (π*I) := by rw [hpi]; linear_combination h
    obtain ⟨l,hl⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    exact ⟨l, by linear_combination -hl⟩
  · rintro ⟨l,rfl⟩
    have he : Complex.exp ((s:ℂ)+(2*(l:ℂ)+1)*π*I-(s:ℂ)) = Complex.exp (π*I) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      exact ⟨l,by ring⟩
    rw [he,hpi]; ring

/-- The logistic derivative with reversed sign is analytic off the literal odd poles. -/
theorem negative_logistic_slope_analytic (s : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ => -Complex.exp (w-s)/(1+Complex.exp (w-s))^2)
      (Set.range (fun l : ℤ => (s:ℂ)+(2*(l:ℂ)+1)*π*I))ᶜ := by
  intro w hw
  have he : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v-s)) w :=
    analyticAt_cexp.comp (analyticAt_id.sub analyticAt_const)
  apply he.neg.div ((analyticAt_const.add he).pow 2)
  exact pow_ne_zero _ (fun h => hw ((logistic_denominator_zero_iff s w).mp h))

#print axioms logistic_denominator_zero_iff
#print axioms negative_logistic_slope_analytic
end OpenMathResearch.LongCycleExcedances
