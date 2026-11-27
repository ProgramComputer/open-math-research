import LinearSlabs
import ScaledMultipleBudget
import CutoffAtomGeometry
import RepositoryRegularCost

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial Real CycleProbability

def literalMultipleAt (k n b t : ℕ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) :=
  ((markedMultiple (A.erase a) (literalMarkedPrimitive k (n+1) (cos θ) (sin θ) a)).coeff b).coeff t

theorem literal_multiple_scaled_bound (slab : Fin 9) {k n b : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) {θ : ℝ} (hS : 0 < sin θ)
    (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (a : ℤ) (t : ℕ) (q : ℕ→ℕ)
    (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale)
    (hb : 0 < b) (h240 : b ≤ 240) :
    literalMultipleAt k n b t θ A a ≤ ((linearSlabLower slab:ℝ)/((k:ℝ)*sin θ))*
      (((q b:ℝ)-(linearSlabTable slab b:ℝ))/linearScale) := by
  let T := A.erase a
  let p := fun v => forgetDegree (literalMarkedPrimitive k (n+1) (cos θ) (sin θ) a v)
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hk : 0 < k := by have := hnX.trans (Nat.mul_le_mul_right k hx); omega
  have hA : 0 < (linearSlabLower slab:ℝ) := by fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  have hKS : 0 < (k:ℝ)*sin θ := by positivity
  have hu := (div_le_one hKS).mpr (linearSlabInputs slab hn hnX hS hU).2
  have hmarked := (marked_bin_bounds T k (n+1)
    (fun v s => ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k (cos θ) (sin θ) a v)‖)
    (fun _ _ _ => norm_nonneg _) b t).2
  apply hmarked.trans
  apply scaled_multiple_budget T p _ _ (by decide : 0 < linearScale) (linearSlabTable slab) q
    (by simp [linearSlabTable,literalLinearTable]) hq (by positivity) hu _ hrec hb h240
  · intro v _ i
    dsimp [p,literalMarkedPrimitive]
    rw [coeff_forgetDegree_markDegreeBin]
    exact sum_nonneg (fun _ _ => by split <;> positivity)
  · intro v _
    dsimp [p,literalMarkedPrimitive]
    rw [coeff_forgetDegree_markDegreeBin]
    apply sum_eq_zero
    intro s hs
    have hh := (degreeBin_bounds hk (mem_Icc.mp hs).1).1
    apply if_neg
    intro he
    rw [he,Nat.mul_zero] at hh
    have := (mem_Icc.mp hs).1
    omega
  · exact fun i _ => literal_slab_scaled_linear_envelope_of_spec slab hn hnX hS hU hd A a i

#print axioms literal_multiple_scaled_bound
end OpenMathResearch.LongCycleExcedances
