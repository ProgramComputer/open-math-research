import WeightedMarkedBins
import CenteredBinGeometry
import PrincipalAdjacentError

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial CycleProbability

def markedAbsoluteProduct {ι : Type*} (A : Finset ι) (k N : ℕ) (F : ι→PowerSeries ℂ) : ℝ[X][X] :=
  ∏ q ∈ A, (1+markDegreeBin k N (fun s => ‖PowerSeries.coeff (R := ℂ) s (F q)‖))

def markedCost (P : ℝ[X][X]) (lower : ℕ) : ℝ :=
  ∑ b ∈ range (P.natDegree+1), centeredErrorBound (centeredBinIndex lower b)*(forgetDegree P).coeff b

theorem centered_marked_partial {ι : Type*} (A : Finset ι) (F : ι→PowerSeries ℂ)
    {m n lower : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d) (hk : 100 ≤ m+1) (hlo : lower*(m+1) ≤ n)
    (hF : ∀ i ∈ A, ∀ t < m+1, PowerSeries.coeff (R := ℂ) t (F i)=0) (N : ℕ) :
    let Q := ∏ q ∈ A, (1+F q)
    (∑ t ∈ range (N+1), (((m:ℝ)+1)*|cutoffWeight (m+1) d (n-t)-Real.exp (-cycleHarmonic m)|)*
      ‖PowerSeries.coeff (R := ℂ) t Q‖) ≤ markedCost (markedAbsoluteProduct A (m+1) N F) lower := by
  let P := markedAbsoluteProduct A (m+1) N F
  let weight (t:ℕ) := ((m:ℝ)+1)*|cutoffWeight (m+1) d (n-t)-Real.exp (-cycleHarmonic m)|
  have hP := marked_product_geometry A (by omega : 0 < m+1) N
    (fun q t => ‖PowerSeries.coeff (R := ℂ) t (F q)‖) (fun _ _ _ => norm_nonneg _)
  apply le_trans _ (weighted_marked_cost P N weight _ hP.1
    (fun b => centeredErrorBound_nonneg (centeredBinIndex lower b)) _)
  · apply sum_le_sum
    intro t ht
    have h := marked_product_dominates A (m+1) N F hF (t:=t) (by have := mem_range.mp ht; omega)
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · intro b t _ hbt
    exact centered_probability_on_bin hd hk hlo (hP.2 b t hbt).1

/-- Bounding the total bin costs uniformly for every primitive truncation
controls the exact untruncated principal convolution. -/
theorem centered_marked_cost {ι : Type*} (A : Finset ι) (F : ι→PowerSeries ℂ)
    {m n lower : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d) (hk : 100 ≤ m+1) (hlo : lower*(m+1) ≤ n)
    (hF : ∀ i ∈ A, ∀ t < m+1, PowerSeries.coeff (R := ℂ) t (F i)=0)
    {w value : ℂ} (hw : ‖w‖=1) (hQ : CoeffHasSum (∏ q ∈ A, (1+F q)) w value) {E : ℝ}
    (hcost : ∀ N, markedCost (markedAbsoluteProduct A (m+1) N F) lower ≤ E) :
    let Q := ∏ q ∈ A, (1+F q)
    ‖((m:ℝ)+1:ℂ)*((∑ t ∈ range (n+1), (cutoffWeight (m+1) d (n-t):ℂ)*
       (PowerSeries.coeff (R := ℂ) t Q*w^t))-(Real.exp (-cycleHarmonic m):ℂ)*value)‖ ≤ E := by
  let Q := ∏ q ∈ A, (1+F q)
  let p (s:ℕ) : ℂ := (cutoffWeight (m+1) d s:ℂ)
  let c := Real.exp (-cycleHarmonic m)
  let K : ℝ := (m:ℝ)+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he := (principal_error_hasSum hQ p (c:ℂ) n).mul_left (K:ℂ)
  have hlim := (he.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)).norm
  have hcast : ((m:ℝ)+1:ℂ) = (K:ℂ) := by simp [K]
  dsimp only
  rw [hcast]
  apply le_of_tendsto hlim (Filter.Eventually.of_forall _)
  intro N
  simp only [Function.comp_apply]
  apply (norm_sum_le _ _).trans
  apply le_trans _ ((centered_marked_partial A F hd hk hlo hF N).trans (hcost N))
  apply sum_le_sum
  intro t _
  have heq : zeroLeft p n t = p (n-t) := by
    by_cases ht : t ≤ n
    · simp [zeroLeft,ht]
    · simp [zeroLeft,ht,Nat.sub_eq_zero_of_le (le_of_not_ge ht),p,cutoffWeight]
  simp only [heq,norm_mul,norm_pow,hw,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK]
  have hc : ‖p (n-t)-(c:ℂ)‖ = |cutoffWeight (m+1) d (n-t)-c| := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [hc]
  dsimp only [K,c,Q]
  linarith only [le_of_eq (mul_assoc ((m:ℝ)+1) |cutoffWeight (m+1) d (n-t)-Real.exp (-cycleHarmonic m)|
      ‖PowerSeries.coeff (R := ℂ) t (∏ q ∈ A,(1+F q))‖).symm]

#print axioms centered_marked_partial
#print axioms centered_marked_cost
end OpenMathResearch.LongCycleExcedances
