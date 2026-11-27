import LiteralBin

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- Exact integral bin bounds. The sum of atom bins, not the ceiling of
the total degree, is the bin of a product. -/
theorem degreeBin_bounds {k s : ℕ} (hk : 0 < k) (hs : k ≤ s) :
    4*s ≤ k*degreeBin k s ∧ k*degreeBin k s ≤ 5*s := by
  let n := 4*s+k-1
  have heq := Nat.div_add_mod n k
  have hlt := Nat.mod_lt n hk
  have hle : k*(n/k) ≤ n := by omega
  change 4*s ≤ k*(n/k) ∧ k*(n/k) ≤ 5*s
  dsimp [n] at *
  omega

private def BinSupport (k : ℕ) (F : ℝ[X][X]) : Prop :=
  ∀ b d, (F.coeff b).coeff d ≠ 0 → 4*d ≤ k*b ∧ k*b ≤ 5*d

private theorem binSupport_sum {ι : Type*} (A : Finset ι) {k : ℕ} (F : ι → ℝ[X][X])
    (h : ∀ q ∈ A, BinSupport k (F q)) : BinSupport k (∑ q ∈ A, F q) := by
  intro b d h0
  by_contra hn
  apply h0
  simp only [finsetSum_coeff]
  exact sum_eq_zero (fun q hq => not_not.mp (fun hh => hn (h q hq b d hh)))

private theorem binSupport_mul {k : ℕ} {F G : ℝ[X][X]} (hF : BinSupport k F)
    (hG : BinSupport k G) : BinSupport k (F*G) := by
  intro b d hb
  by_contra hn
  apply hb
  simp only [coeff_mul,finsetSum_coeff]
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  have hi' := mem_antidiagonal.mp hi
  have hj' := mem_antidiagonal.mp hj
  by_contra! h
  have h1 := hF _ _ (left_ne_zero_of_mul h)
  have h2 := hG _ _ (right_ne_zero_of_mul h)
  apply hn
  rw [← hi',← hj',Nat.mul_add,Nat.mul_add,Nat.mul_add]
  omega

private theorem binSupport_one {k : ℕ} : BinSupport k (1:ℝ[X][X]) := by
  intro b d h
  have hb : b=0 := by by_contra! nh; simp [coeff_one,nh] at h
  have hd : d=0 := by by_contra! nh; simp [coeff_one,hb,nh] at h
  simp [hb,hd]

private theorem binSupport_prod {ι : Type*} (A : Finset ι) {k : ℕ} (F : ι → ℝ[X][X])
    (h : ∀ q ∈ A, BinSupport k (F q)) : BinSupport k (∏ q ∈ A, F q) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using (binSupport_one (k:=k))
  | @insert a A ha ih =>
    rw [prod_insert ha]
    exact binSupport_mul (h a (mem_insert_self ..))
      (ih (fun q hq => h q (mem_insert_of_mem hq)))

private theorem binSupport_mark (k N : ℕ) (hk : 0 < k) (c : ℕ → ℝ) :
    BinSupport k (markDegreeBin k N c) := by
  intro b d h
  rw [coeff_markDegreeBin] at h
  split at h
  next hd =>
    rw [← hd.2]
    exact degreeBin_bounds hk (mem_Icc.mp hd.1).1
  simp at h

/-- The selected multiple-primitive coefficient vanishes if its total degree
cannot belong to the selected summed bin. -/
theorem literal_multiple_support (A : Finset ℤ) {k : ℕ} (hk : 0 < k) (N : ℕ)
    (C S : ℝ) (a : ℤ) {b d : ℕ}
    (hn : ¬(4*d ≤ k*b ∧ k*b ≤ 5*d)) :
    ((markedMultiple (A.erase a) (literalMarkedPrimitive k N C S a)).coeff b).coeff d = 0 := by
  by_contra! hb
  apply hn
  apply binSupport_sum _ _ (fun T _ => binSupport_prod T _ (fun j _ => binSupport_mark k N hk _)) b d hb

/-- Both integral degree inequalities for the full product, including its constant term. -/
theorem marked_full_degree_support {ι : Type*} (A : Finset ι) {k : ℕ} (hk : 0 < k) (N : ℕ)
    (c : ι → ℕ→ℝ) : ∀ b d,
      ((∏ q ∈ A, (1+markDegreeBin k N (c q))).coeff b).coeff d ≠ 0 → 4*d ≤ k*b ∧ k*b ≤ 5*d := by
  classical
  apply binSupport_prod
  intro q _
  intro b d hh
  simp only [coeff_add] at hh
  by_cases h : ((1:ℝ[X][X]).coeff b).coeff d=0
  · rw [h,zero_add] at hh
    exact binSupport_mark k N hk _ b d hh
  · exact binSupport_one b d h


#print axioms marked_full_degree_support

#print axioms degreeBin_bounds
#print axioms literal_multiple_support
end OpenMathResearch.LongCycleExcedances
