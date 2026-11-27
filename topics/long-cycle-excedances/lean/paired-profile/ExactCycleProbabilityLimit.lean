import EntireCycleEvaluation
import PrincipalHarmonic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open Filter Finset
open scoped Topology PowerSeries

/-- Summing the actual numerator at one identifies the probability limit. -/
theorem numeratorDiff_hasSum_limit (m : ℕ) {d : ℕ → ℝ} (hd : Spec (m+1) d) :
    HasSum (numeratorDiff (m+1) d) (Real.exp (-cycleHarmonic m)) := by
  have hh := cutoff_numerator_hasSum m (1:ℂ)
  unfold CoeffHasSum at hh
  have hcoef (n : ℕ) := coeff_cutoffCycleNumerator_eq_of_spec (s:=n) hd (by omega : 0 < m+1)
  have hs : HasSum (fun n => ((numeratorDiff (m+1) d n : ℝ):ℂ))
      ((Real.exp (-cycleHarmonic m):ℝ):ℂ) := by
    convert hh using 1
    · funext n
      simp [hcoef]
    · simp [cycleHarmonic,Complex.ofReal_exp,Complex.ofReal_sum,Complex.ofReal_div]
  exact (RCLike.hasSum_ofReal ℂ).mp hs

private theorem partial_differences (m N : ℕ) (d : ℕ→ℝ) :
    (∑ s ∈ range (N+1), numeratorDiff (m+1) d s) = cutoffWeight (m+1) d N := by
  induction N with
  | zero => simp [numeratorDiff,cutoffWeight]
  | succ N ih =>
    rw [sum_range_succ,ih,numeratorDiff,Nat.add_sub_cancel]
    ring

theorem probability_tends_to_harmonic (m : ℕ) {d : ℕ→ℝ} (hd : Spec (m+1) d) :
    Tendsto d atTop (𝓝 (Real.exp (-cycleHarmonic m))) := by
  have hs := (numeratorDiff_hasSum_limit m hd).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (m+1)] with n hn
  change ∑ s ∈ range (n+1), numeratorDiff (m+1) d s = d n
  rw [partial_differences,cutoffWeight,if_pos hn]

theorem probability_limit_band {m : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d) (hk : 100 ≤ m+1) :
    548/1000 ≤ ((m:ℝ)+1)*Real.exp (-cycleHarmonic m) ∧
      ((m:ℝ)+1)*Real.exp (-cycleHarmonic m) ≤ 4/7 := by
  have ht := (probability_tends_to_harmonic m hd).const_mul ((m:ℝ)+1)
  constructor
  · apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop (3*(m+1))] with n hn
    simpa using (lower548 hd (by omega) n hn).le
  · apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop (2*(m+1))] with n hn
    simpa using upper47 hd hk n hn

theorem probability_tail_identity (m N : ℕ) {d : ℕ→ℝ} (hd : Spec (m+1) d) :
    Real.exp (-cycleHarmonic m)-cutoffWeight (m+1) d N =
      ∑' i, numeratorDiff (m+1) d (i+(N+1)) := by
  have hh := numeratorDiff_hasSum_limit m hd
  have he := hh.summable.sum_add_tsum_nat_add (N+1)
  rw [partial_differences,hh.tsum_eq] at he
  linarith

#print axioms numeratorDiff_hasSum_limit
#print axioms probability_tends_to_harmonic
#print axioms probability_limit_band
#print axioms probability_tail_identity
end OpenMathResearch.LongCycleExcedances.CycleProbability
