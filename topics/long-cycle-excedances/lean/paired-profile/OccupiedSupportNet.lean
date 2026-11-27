import PairedPoleConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Finset
open scoped Topology

/-- The support net over finite pole sets exhausts every finite set of marked
configurations, with any specified finite support map. -/
theorem hasSum_comp_finite_support {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {f : J → ℂ} {z : ℂ} (hf : HasSum f z)
    (support : J → Finset ι) (slice : Finset ι → Finset J)
    (hs : ∀ A j, j ∈ slice A ↔ support j ⊆ A) :
    Tendsto (fun A => ∑ j ∈ slice A, f j) atTop (𝓝 z) := by
  have h : Tendsto slice atTop atTop := by
    apply tendsto_atTop.2
    intro F
    filter_upwards [eventually_ge_atTop (F.biUnion support)] with A hA
    intro j hj
    apply (hs _ _).2
    intro i hi
    exact hA (mem_biUnion.mpr ⟨j,hj,hi⟩)
  have hsum : Tendsto (fun F : Finset J => ∑ j ∈ F, f j) atTop (𝓝 z) := by
    simpa only [HasSum, SummationFilter.unconditional] using hf
  exact hsum.comp h

/-- A product of positive summable activities, indexed by each finite
subset exactly once, is summable. The bound comes from `prod_one_add`. -/
theorem summable_occupied_finset {ι : Type*} [DecidableEq ι]
    {w : ι → ℝ} (hw : Summable w) (h0 : ∀ i, 0 ≤ w i) :
    Summable (fun s : Finset ι => ∏ i ∈ s, w i) := by
  apply summable_of_sum_le (c := Real.exp (∑' i, w i))
    (fun _ => prod_nonneg (fun i _ => h0 i))
  intro F
  let U := F.biUnion id
  have hsub : F ⊆ U.powerset := by
    intro t ht
    exact mem_powerset.mpr (fun i hi => mem_biUnion.mpr ⟨t,ht,hi⟩)
  calc
    _ ≤ ∑ t ∈ U.powerset, ∏ i ∈ t, w i :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => prod_nonneg (fun i _ => h0 i))
    _ = ∏ i ∈ U, (1+w i) := (prod_one_add U).symm
    _ ≤ ∏ i ∈ U, Real.exp (w i) :=
      prod_le_prod (fun i _ => by linarith [h0 i]) (fun i _ => by simpa [add_comm] using Real.add_one_le_exp (w i))
    _ = Real.exp (∑ i ∈ U, w i) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hw.sum_le_tsum U (fun i _ => h0 i))

#print axioms hasSum_comp_finite_support
#print axioms summable_occupied_finset
end OpenMathResearch.LongCycleExcedances
