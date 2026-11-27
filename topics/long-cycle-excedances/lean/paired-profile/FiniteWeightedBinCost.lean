import PrincipalBinHeadTail

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- Weights supported on the first J bins have an exact finite comparison
with the rounded product recurrence without a geometric tail. -/
theorem finite_weighted_bin_cost (A : Finset ℤ) (a : ℤ) {k N J G : ℕ} (hk : 0 < k)
    (C S : ℝ) (hF : ∀ v ∈ A.erase a, ∀ t < k, PowerSeries.coeff (R := ℂ) t (occupiedPrimitive k C S a v)=0)
    (weight budget : ℕ→ℝ) (hw : ∀ t, 0 ≤ weight t) (hb : ∀ b, 0 ≤ budget b)
    (hcut : ∀ b, J < b → budget b=0)
    (hjoin : ∀ b t, t ≤ N → 4*t ≤ k*b → k*b ≤ 5*t → weight t ≤ budget b)
    (hG : 0 < G) (l q : ℕ→ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ i ≤ J, (binLinear (A.erase a) (fun v => forgetDegree (literalMarkedPrimitive k N C S a v))).coeff i
      ≤ (l i:ℝ)/G)
    (hrec : ∀ m < J, ∑ ij ∈ antidiagonal m,(ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G) :
    (∑ t ∈ range (N+1), weight t*
      ‖PowerSeries.coeff (R := ℂ) t (∏ v ∈ A.erase a, (1+occupiedPrimitive k C S a v))‖) ≤
        ∑ b ∈ range (J+1), budget b*((q b:ℝ)/G) := by
  let P := markedAbsoluteProduct (A.erase a) k N (occupiedPrimitive k C S a)
  let p (v:ℤ) := forgetDegree (literalMarkedPrimitive k N C S a v)
  have hgeom := marked_product_geometry (A.erase a) hk N
    (fun v t => ‖PowerSeries.coeff (R := ℂ) t (occupiedPrimitive k C S a v)‖) (fun _ _ _ => norm_nonneg _)
  have hf (b t : ℕ) (ht : t ≤ N) (hbt : (P.coeff b).coeff t≠0) : weight t ≤ budget b :=
    hjoin b t ht (hgeom.2 b t hbt).1 (hgeom.2 b t hbt).2
  have h1 := weighted_marked_cost P N weight budget hgeom.1 hb hf
  have heq : forgetDegree P = binFull (A.erase a) p := forget_marked_absolute_product ..
  have hq' := literal_rounded_head_bound A a hk C S hG l q hl hq hL hrec
  apply le_trans _ (h1.trans _)
  · apply sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (marked_product_dominates (A.erase a) k N _ hF
      (by have := mem_range.mp ht; omega)) (hw t)
  · let D := range (P.natDegree+1)
    let v := fun b => if b ≤ J then budget b*((q b:ℝ)/G) else 0
    have hterm (b:ℕ) : budget b*(forgetDegree P).coeff b ≤ v b := by
      dsimp only [v]
      split
      next h => rw [heq]; exact mul_le_mul_of_nonneg_left (hq' b h) (hb b)
      next h => rw [hcut b (lt_of_not_ge h),zero_mul]
    apply (sum_le_sum (s:=D) (fun b _ => hterm b)).trans
    rw [show (∑ b ∈ D, v b)=∑ b ∈ D.filter (· ≤ J), budget b*((q b:ℝ)/G) by rw [sum_filter]]
    apply sum_le_sum_of_subset_of_nonneg
    · intro b h
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp h).2)
    · intro b _ _
      exact mul_nonneg (hb b) (by positivity)

#print axioms finite_weighted_bin_cost
end OpenMathResearch.LongCycleExcedances
