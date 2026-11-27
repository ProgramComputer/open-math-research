import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Set Filter
open scoped Topology

/-- A real-ray identity extends throughout the complement of a countable
complex pole set. The threshold itself must avoid the poles. -/
theorem analytic_eq_off_poles_of_real_ray {P : Set ℂ} (hP : P.Countable) {s : ℝ}
    (hs : (s:ℂ) ∉ P) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Pᶜ)
    (hg : AnalyticOnNhd ℂ g Pᶜ) (hreal : ∀ x : ℝ, x < s → f (x:ℂ) = g (x:ℂ)) :
    Set.EqOn f g Pᶜ := by
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  apply hf.eqOn_of_preconnected_of_frequently_eq hg
    (hP.isConnected_compl_of_one_lt_rank hdim).isPreconnected hs
  have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[<] s) (𝓝[≠] (s:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun he => (ne_of_lt hx) (Complex.ofReal_inj.mp he)
  have hleft : ∀ᶠ (x : ℝ) in 𝓝[<] s, f (x:ℂ)=g (x:ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hreal x hx
  exact hmap.frequently hleft.frequently

#print axioms analytic_eq_off_poles_of_real_ray
end OpenMathResearch.LongCycleExcedances
