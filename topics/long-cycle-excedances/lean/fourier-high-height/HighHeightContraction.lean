import PoissonRadiusBounds
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Filter Topology

theorem radial_tsum_bound (k : ℕ) (s R D : ℝ) (hs : 0 < s) (hsR : s ≤ R)
    (hk : 0 < k) (hD : 0 ≤ D) (hR : R-s ≤ D*(s/k)) (hc : 0 < 1/50-D/k) :
    Summable (radialFrequency k s R) ∧
      (∑' a, radialFrequency k s R a) ≤
        ((5/4:ℝ)*k/s)*exp (D*(5/4)) + 1/((1/50-D/k)*s) := by
  have hn (a : ℕ) : 0 ≤ radialFrequency k s R a := by
    unfold radialFrequency
    have hR0 : 0 ≤ R := hs.le.trans hsR
    positivity
  have H := radial_frequency_sum k s R D hs hsR hk hD hR hc
  exact ⟨summable_of_sum_le hn H, (summable_of_sum_le hn H).tsum_le_of_sum_le H⟩

def highHeightTail (k : ℕ) (s t : ℝ) (a : ℕ) : ℝ :=
  let A := ((a+1:ℕ):ℝ)
  exp (-A*s)/A * ∑' j : ℕ, (A*t)^(j+k)/((j+k).factorial:ℝ)

theorem high_height_tail_tsum (k : ℕ) (s t : ℝ) (hk : 100 ≤ k) (ht : 1 ≤ t)
    (hgap : (69/100)*s/k ≤ s-t) (hts : t < s) :
    Summable (highHeightTail k s t) ∧
      (∑' a, highHeightTail k s t a) ≤ 1/1000+2/(69/100) := by
  have hd (a : ℕ) :
      Summable (fun j : ℕ => (((a+1:ℕ):ℝ)*t)^(j+k)/((j+k).factorial:ℝ)) := by
    exact (NormedSpace.expSeries_div_hasSum_exp ℝ (((a+1:ℕ):ℝ)*t)).summable.comp_injective
      (add_left_injective k)
  have hn (a : ℕ) : 0 ≤ highHeightTail k s t a := by
    unfold highHeightTail
    have ht0 : 0 ≤ t := by linarith
    exact mul_nonneg (by positivity) (tsum_nonneg (by intro; positivity))
  have HB (F : Finset ℕ) : (∑ a ∈ F, highHeightTail k s t a) ≤ 1/1000+2/(69/100) := by
    let block (N : ℕ) : Finset ℕ := (range N).map ⟨(·+k), add_left_injective k⟩
    have hBlock (N j : ℕ) (hj : j ∈ block N) : k ≤ j := by
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      simp
    have hterm (a : ℕ) : Tendsto (fun N : ℕ => tailFrequency s t (fun _ => block N) a)
        atTop (𝓝 (highHeightTail k s t a)) := by
      have h := (hd a).hasSum.mul_left (exp (-((a+1:ℕ):ℝ)*s)/((a+1:ℕ):ℝ))
      have h' := h.tendsto_sum_nat
      simpa only [highHeightTail, tailFrequency, block, sum_map, Function.Embedding.coeFn_mk, mul_sum] using h'
    exact le_of_tendsto_of_tendsto (tendsto_finset_sum F fun a _ => hterm a) tendsto_const_nhds
      (Eventually.of_forall fun N => tail_frequency_sum k s t hk ht hgap hts F
        (fun _ => block N) (fun _ j hj => hBlock N j hj))
  exact ⟨summable_of_sum_le hn HB, (summable_of_sum_le hn HB).tsum_le_of_sum_le HB⟩

#print axioms radial_tsum_bound
#print axioms high_height_tail_tsum
end OpenMathResearch.LongCycleExcedances
