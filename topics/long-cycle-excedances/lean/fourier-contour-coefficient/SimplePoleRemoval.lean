import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Set
open scoped Topology

/-- Remove the principal part of a ratio with a simple denominator zero. -/
theorem analytic_remove_simple_pole {N D : ℂ → ℂ} {p d : ℂ}
    (hN : AnalyticAt ℂ N p) (hD : AnalyticAt ℂ D p)
    (hzero : D p = 0) (hder : HasDerivAt D d p) (hd : d ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in 𝓝[≠] p, N z / D z - (N p / d) / (z-p) = g z := by
  have hds {f : ℂ → ℂ} (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (dslope f p) p :=
    let ⟨_, h⟩ := hf
    h.has_fpower_series_dslope_fslope.analyticAt
  have hDp : dslope D p p = d := by rw [dslope_same, hder.deriv]
  let F := fun z => N z / dslope D p z
  have hF : AnalyticAt ℂ F p := hN.div (hds hD) (by rwa [hDp])
  refine ⟨dslope F p, hds hF, ?_⟩
  have hneq : ∀ᶠ z in 𝓝[≠] p, dslope D p z ≠ 0 :=
    ((hds hD).continuousAt.eventually_ne (by rwa [hDp])).filter_mono nhdsWithin_le_nhds
  filter_upwards [hneq, self_mem_nhdsWithin] with z hzD hz
  have hz' : z ≠ p := hz
  have he : dslope D p z = D z/(z-p) := by
    rw [dslope_of_ne _ hz']
    simp [slope, hzero, div_eq_inv_mul]
  have hDz : D z ≠ 0 := by
    intro e
    rw [he,e,zero_div] at hzD
    exact hzD rfl
  rw [dslope_of_ne _ hz']
  change _ = (z-p)⁻¹ * (N z / dslope D p z - N p / dslope D p p)
  rw [hDp, he]
  field_simp [sub_ne_zero.mpr hz', hDz, hd]
  <;> ring

#print axioms analytic_remove_simple_pole
end OpenMathResearch.LongCycleExcedances
