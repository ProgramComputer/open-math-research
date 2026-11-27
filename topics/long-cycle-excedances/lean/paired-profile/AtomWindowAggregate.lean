import AtomMultipleCost
import MarkedCoefficientComparison

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset Real CycleProbability

theorem rounded_gap_nonnegative {G N b : ℕ} (hG : 0 < G) (l q : ℕ→ℕ) (hq : q 0=G)
    (hrec : ∀ m < N, ∑ ij ∈ antidiagonal m,(ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G)
    (hb : 0 < b) (hbN : b ≤ N) : l b ≤ q b := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  let f (ij : ℕ×ℕ) := (ij.1+1)*l (ij.1+1)*q ij.2
  have he : (m,0) ∈ antidiagonal m := mem_antidiagonal.mpr (Nat.add_zero m)
  have h := (single_le_sum (f:=f) (fun i _ => Nat.zero_le _) he).trans (hrec m (by omega))
  change (m+1)*l (m+1)*q 0 ≤ (m+1)*q (m+1)*G at h
  rw [hq] at h
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_right h hG) (Nat.succ_pos m)

private theorem finite_marked_degree (P : ℝ[X][X]) (J t : ℕ)
    (h : ∀ b, J < b → (P.coeff b).coeff t=0) :
    (P.eval 1).coeff t = ∑ b ∈ range (J+1), (P.coeff b).coeff t := by
  rw [eval_eq_sum_range' (p:=P) (n:=max P.natDegree J+1) (by omega)]
  simp only [one_pow,mul_one,finsetSum_coeff]
  symm
  apply sum_subset (range_mono (by omega))
  intro b _ hb
  exact h b (by simp only [mem_range] at hb; omega)

def occupiedMultipleResidual (k t : ℕ) (θ : ℝ) (A : Finset ℤ) (a : ℤ) :=
  let F := occupiedPrimitive k (cos θ) (sin θ) a
  PowerSeries.coeff (R := ℂ) t ((∏ v ∈ A.erase a, (1+F v))-1-∑ v ∈ A.erase a, F v)

theorem atom_multiple_one_pole (slab : Fin 9) {k n lower t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    (he : t+k=n+1) {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (a : ℤ) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    ‖occupiedMultipleResidual k t θ A a‖*‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k/sin θ ≤
      ∑ b ∈ range 241, atomMultiplePoleBudget lower (linearSlabX slab) b (linearSlabLower slab) q (linearSlabTable slab) a := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hk : 192 ≤ k := by have := hnX.trans (Nat.mul_le_mul_right k hx); omega
  let P := markedMultiple (A.erase a) (literalMarkedPrimitive k (n+1) (cos θ) (sin θ) a)
  let ρ := ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖
  have hp : ‖occupiedMultipleResidual k t θ A a‖ ≤ (P.eval 1).coeff t :=
    marked_multiple_dominates _ _ _ _ (fun v _ s hs => occupied_primitive_below hd (by omega) hs _ _ a v)
      (show t ≤ n+1 by omega)
  have hcut (b : ℕ) (hb : 240 < b) : (P.coeff b).coeff t=0 := by
    apply literal_multiple_support _ (by omega : 0 < k)
    intro h
    have hh := (atom_bin_interval (by omega : 5 < k) hl hlo hnX he h.1 h.2).2
    omega
  rw [finite_marked_degree P 240 t hcut] at hp
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (pow_nonneg (norm_nonneg _) k)) hS.le).trans
  rw [sum_mul,sum_div]
  exact sum_le_sum (fun b _ => atom_multiple_bin slab hd hn hnX hl hlo he hS hU A a q hq hrec)

#print axioms rounded_gap_nonnegative
#print axioms atom_multiple_one_pole
end OpenMathResearch.LongCycleExcedances
