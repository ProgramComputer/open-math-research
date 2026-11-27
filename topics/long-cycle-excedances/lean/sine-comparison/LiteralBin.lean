import BivariateBin
import BinIntegerCertificate
import ActualOccupiedValue

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

def literalMarkedPrimitive (k N : ℕ) (C S : ℝ) (a q : ℤ) : ℝ[X][X] :=
  markDegreeBin k N (fun s => ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k C S a q)‖)

theorem literalPrimitive_norm_formula {k s : ℕ} (hk : 0 < k) (hs : k ≤ s)
    (C : ℝ) {S : ℝ} (hS : S ≠ 0) (a q : ℤ) :
    ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k C S a q)‖ =
      ‖((pairedPoleDenom C S q)⁻¹)^(s-1) /
        (pairedPoleDenom C S q-pairedPoleDenom C S a) *
        PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X))‖ := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  rw [occupiedPrimitive, finite_cycle_primitive_coeff _ _ (pairedPoleDenom_ne_zero C hS q)]
  simp

theorem coeff_forgetDegree_markDegreeBin (k N : ℕ) (c : ℕ → ℝ) (b : ℕ) :
    (forgetDegree (markDegreeBin k N c)).coeff b =
      ∑ s ∈ Icc k N, if degreeBin k s=b then c s else 0 := by
  rw [forgetDegree, coeff_map, markDegreeBin, finsetSum_coeff]
  change (∑ s ∈ Icc k N, ((monomial (degreeBin k s)) ((monomial s) (c s))).coeff b).eval 1 = _
  rw [eval_finsetSum]
  apply sum_congr rfl
  intro s _
  rw [coeff_monomial]
  by_cases h : degreeBin k s=b <;> simp [h,eval_monomial]

private theorem degreeBin_pos {k s : ℕ} (hk : 0 < k) (hs : k ≤ s) :
    0 < degreeBin k s := by
  unfold degreeBin
  apply (Nat.le_div_iff_mul_le hk).2
  have h := Nat.mul_le_mul_left 4 hs
  omega

theorem literal_occupied_bin_integer_bound (A : Finset ℤ)
    {k N G J : ℕ} (hk : 0 < k) (C S : ℝ) (a : ℤ)
    (hG : 0 < G) (l q : ℕ → ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ b ≤ J, (binLinear (A.erase a)
      (fun v => forgetDegree (literalMarkedPrimitive k N C S a v))).coeff b ≤ (l b:ℝ)/G)
    (hrec : ∀ m < J, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤
        (m+1)*q (m+1)*G) {b : ℕ} (hb : 0 < b) (hbJ : b ≤ J) (d : ℕ) :
    let P := literalMarkedPrimitive k N C S a
    (((∏ v ∈ A.erase a, (1+P v)).coeff b).coeff d ≤ (q b:ℝ)/G) ∧
      (((markedMultiple (A.erase a) P).coeff b).coeff d ≤ ((q b:ℝ)-(l b:ℝ))/G) := by
  dsimp only
  let P := literalMarkedPrimitive k N C S a
  let p := fun v => forgetDegree (P v)
  have hp (v : ℤ) (_ : v ∈ A.erase a) (j : ℕ) : 0 ≤ (p v).coeff j := by
    dsimp [p,P,literalMarkedPrimitive]
    rw [coeff_forgetDegree_markDegreeBin]
    exact sum_nonneg (fun s _ => by split <;> positivity)
  have hz (v : ℤ) (_ : v ∈ A.erase a) : (p v).coeff 0=0 := by
    dsimp [p,P,literalMarkedPrimitive]
    rw [coeff_forgetDegree_markDegreeBin]
    exact sum_eq_zero (fun s hs => if_neg (degreeBin_pos hk (mem_Icc.mp hs).1).ne')
  have h₁ := marked_bin_bounds (A.erase a) k N
    (fun v s => ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k C S a v)‖)
    (fun _ _ _ => norm_nonneg _) b d
  have h₂ := bin_integer_multiple_bound (A.erase a) p hp hz hG l q hl hq hL hrec hb hbJ
  exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

#print axioms literalPrimitive_norm_formula
#print axioms coeff_forgetDegree_markDegreeBin
#print axioms literal_occupied_bin_integer_bound
end OpenMathResearch.LongCycleExcedances
