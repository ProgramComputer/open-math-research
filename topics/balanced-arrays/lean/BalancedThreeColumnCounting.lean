import BalancedThreeColumnPrefix
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Pi

/-!
# Inclusion-exclusion from column supports

The three columns are subsets of the finite set of row labels. Row cap two
is precisely the condition that the intersection of all three is empty.
-/

namespace BalancedThreeColumnCounting

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The possible column supports of cardinality k. -/
def columnSupports (k : ℕ) : Finset (Finset α) := univ.powersetCard k

/-- The remaining two columns when the third support K is prescribed. -/
def allowedPairs (k : ℕ) (K : Finset α) : Finset (Finset α × Finset α) :=
  ((columnSupports k : Finset (Finset α)) ×ˢ columnSupports k).filter
    (fun p => K ∩ p.1 ∩ p.2 = ∅)

/-- A three-column balanced array written by its three support sets. -/
def allowedTriples (k : ℕ) : Finset (Sigma (fun _ : Finset α => Finset α × Finset α)) :=
  (columnSupports k).sigma (allowedPairs k)

private def supersets (k : ℕ) (J : Finset α) : Finset (Finset α) :=
  (columnSupports k).filter (fun A => J ⊆ A)

private theorem supersets_card (k : ℕ) (J : Finset α) (hJ : J.card ≤ k) :
    (supersets k J).card = (Fintype.card α - J.card).choose (k - J.card) := by
  let extras := ((univ : Finset α) \ J).powersetCard (k - J.card)
  have hExtras (A : Finset α) (hA : A ∈ extras) :
      A ⊆ (univ : Finset α) \ J ∧ A.card = k - J.card := mem_powersetCard.mp hA
  have hdisj (A : Finset α) (hA : A ∈ extras) : Disjoint A J :=
    ((disjoint_sdiff : Disjoint J ((univ : Finset α) \ J)).mono_right (hExtras A hA).1).symm
  have hcancel (A : Finset α) (hA : A ∈ extras) : (A ∪ J) \ J = A := by
    rw [union_sdiff_distrib, sdiff_eq_self_of_disjoint (hdisj A hA), sdiff_self]
    simp
  have hbij : extras.card = (supersets k J).card := by
    refine card_bij (fun A _ => A ∪ J) ?_ ?_ ?_
    · intro A hA
      rw [supersets, mem_filter, columnSupports, mem_powersetCard]
      refine ⟨⟨subset_univ _, ?_⟩, subset_union_right⟩
      rw [card_union_of_disjoint (hdisj A hA), (hExtras A hA).2, Nat.sub_add_cancel hJ]
    · intro A hA B hB hAB
      change A ∪ J = B ∪ J at hAB
      calc
        A = (A ∪ J) \ J := (hcancel A hA).symm
        _ = (B ∪ J) \ J := by rw [hAB]
        _ = B := hcancel B hB
    · intro A hA
      rw [supersets, mem_filter, columnSupports, mem_powersetCard] at hA
      refine ⟨A \ J, mem_powersetCard.mpr ⟨?_, ?_⟩, sdiff_union_of_subset hA.2⟩
      · intro a ha
        exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ha).2⟩
      · rw [card_sdiff hA.2, hA.1.2]
  rw [← hbij, show extras = ((univ : Finset α) \ J).powersetCard (k - J.card) from rfl,
    card_powersetCard, card_sdiff (subset_univ J), card_univ]

omit [Fintype α] in
private theorem powerset_common (K A B : Finset α) :
    (K ∩ A ∩ B).powerset = K.powerset.filter (fun J => J ⊆ A ∧ J ⊆ B) := by
  ext J
  simp only [mem_powerset, mem_filter, subset_inter_iff]
  tauto

/-- For any fixed third support of size k, the normalized inclusion-exclusion
coefficient is exactly the count of allowed first and second supports. -/
theorem allowedPairs_card (k : ℕ) (K : Finset α) (hK : K.card = k) :
    ((allowedPairs k K).card : ℤ) =
      BalancedThreeColumnPrefix.inclusionExclusion (Fintype.card α) k := by
  let base : Finset (Finset α × Finset α) := columnSupports k ×ˢ columnSupports k
  calc
    ((allowedPairs k K).card : ℤ) = ∑ p ∈ allowedPairs k K, (1 : ℤ) := by simp
    _ = ∑ p ∈ base, if K ∩ p.1 ∩ p.2 = ∅ then (1 : ℤ) else 0 := by
      rw [allowedPairs, sum_filter]
    _ = ∑ p ∈ base, ∑ J ∈ (K ∩ p.1 ∩ p.2).powerset, (-1 : ℤ) ^ J.card := by
      apply sum_congr rfl
      intro p _
      rw [sum_powerset_neg_one_pow_card]
    _ = ∑ p ∈ base, ∑ J ∈ K.powerset,
        if J ⊆ p.1 ∧ J ⊆ p.2 then (-1 : ℤ) ^ J.card else 0 := by
      apply sum_congr rfl
      intro p _
      rw [powerset_common, sum_filter]
    _ = ∑ J ∈ K.powerset, (-1 : ℤ) ^ J.card *
        (((Fintype.card α - J.card).choose (k - J.card) : ℕ) : ℤ) ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro J hJ
      have hjk : J.card ≤ k := hK ▸ card_le_card (mem_powerset.mp hJ)
      rw [← sum_filter, show base = columnSupports k ×ˢ columnSupports k from rfl,
        filter_product, ← show supersets k J = (columnSupports k).filter (fun A => J ⊆ A) from rfl,
        sum_const, card_product, supersets_card k J hjk]
      simp only [nsmul_eq_mul, Nat.cast_mul, pow_two]
      ring
    _ = BalancedThreeColumnPrefix.inclusionExclusion (Fintype.card α) k := by
      rw [sum_powerset_apply_card (fun j => (-1 : ℤ) ^ j *
        ((Fintype.card α - j).choose (k - j) : ℤ) ^ 2), hK]
      unfold BalancedThreeColumnPrefix.inclusionExclusion
      apply sum_congr rfl
      intro j _
      rw [nsmul_eq_mul]
      ring

/-- Without fixing a third column, multiply the normalized count by
the number of choices for that column. -/
theorem allowedTriples_card (k : ℕ) :
    ((allowedTriples (α := α) k).card : ℤ) =
      (Fintype.card α).choose k *
        BalancedThreeColumnPrefix.inclusionExclusion (Fintype.card α) k := by
  rw [allowedTriples, card_sigma, Nat.cast_sum]
  calc
    ∑ K ∈ (columnSupports k : Finset (Finset α)), ((allowedPairs k K).card : ℤ)
        = ∑ _ ∈ (columnSupports k : Finset (Finset α)),
            BalancedThreeColumnPrefix.inclusionExclusion (Fintype.card α) k := by
          apply sum_congr rfl
          intro K hK
          exact allowedPairs_card k K (mem_powersetCard.mp hK).2
    _ = _ := by simp [columnSupports, card_powersetCard, nsmul_eq_mul]

section Matrices

/-- Zero-one matrices on the labeled rows and three column indices. -/
abbrev BinaryArray (n : ℕ) := Fin n → Fin 3 → Bool

/-- The support of a specific column. -/
def supportOf {n : ℕ} (a : BinaryArray n) (c : Fin 3) : Finset (Fin n) :=
  univ.filter (fun i => a i c = true)

/-- Finite set of balanced binary arrays with the original row cap and quotas. -/
def binaryArrays (n k : ℕ) : Finset (BinaryArray n) :=
  univ.filter (fun a => (∀ c, (supportOf a c).card = k) ∧
    ∀ i, ((univ : Finset (Fin 3)).filter (fun c => a i c = true)).card ≤ 2)

private abbrev Supports (n : ℕ) :=
  Sigma (fun _ : Finset (Fin n) => Finset (Fin n) × Finset (Fin n))

private def toSupports {n : ℕ} (a : BinaryArray n) : Supports n :=
  ⟨supportOf a 2, supportOf a 0, supportOf a 1⟩

private def fromSupports {n : ℕ} (s : Supports n) : BinaryArray n :=
  fun i c => if c = 0 then decide (i ∈ s.2.1) else
    if c = 1 then decide (i ∈ s.2.2) else decide (i ∈ s.1)

private theorem row_cap_iff (row : Fin 3 → Bool) :
    ((univ : Finset (Fin 3)).filter (fun c => row c = true)).card ≤ 2 ↔
    ¬ (row 0 = true ∧ row 1 = true ∧ row 2 = true) := by
  have hall : (∀ c, row c = true) ↔
      (row 0 = true ∧ row 1 = true ∧ row 2 = true) := by
    constructor
    · exact fun h => ⟨h 0, h 1, h 2⟩
    · rintro ⟨h₀, h₁, h₂⟩ c
      fin_cases c
      · exact h₀
      · exact h₁
      · exact h₂
  rw [← hall]
  let E := (univ : Finset (Fin 3)).filter (fun c => row c = true)
  have huniv : (univ : Finset (Fin 3)).card = 3 := by simp
  change E.card ≤ 2 ↔ ¬ (∀ c, row c = true)
  constructor
  · intro h hr
    have heq : E = univ := by ext c; simp [E, hr]
    rw [heq, huniv] at h
    omega
  · intro h
    by_contra hgt
    have hb : (univ : Finset (Fin 3)).card ≤ E.card := by omega
    have heq : E = univ := eq_of_subset_of_card_le (subset_univ _) hb
    apply h
    intro c
    have hc : c ∈ E := heq.symm ▸ mem_univ c
    exact (mem_filter.mp hc).2

private theorem toSupports_mem_iff {n k : ℕ} (a : BinaryArray n) :
    toSupports a ∈ allowedTriples (α := Fin n) k ↔ a ∈ binaryArrays n k := by
  have hcols : (∀ c, (supportOf a c).card = k) ↔
      ((supportOf a 0).card = k ∧ (supportOf a 1).card = k ∧ (supportOf a 2).card = k) := by
    constructor
    · exact fun h => ⟨h 0, h 1, h 2⟩
    · rintro ⟨h₀, h₁, h₂⟩ c
      fin_cases c
      · exact h₀
      · exact h₁
      · exact h₂
  have hcap : (∀ i, ((univ : Finset (Fin 3)).filter (fun c => a i c = true)).card ≤ 2) ↔
      supportOf a 2 ∩ supportOf a 0 ∩ supportOf a 1 = ∅ := by
    simp only [row_cap_iff, eq_empty_iff_forall_not_mem, mem_inter, supportOf, mem_filter,
      mem_univ, true_and]
    constructor
    · intro h i hi
      exact h i ⟨hi.1.2, hi.2, hi.1.1⟩
    · intro h i hi
      exact h i ⟨⟨hi.2.2, hi.1⟩, hi.2.1⟩
  simp only [toSupports, allowedTriples, mem_sigma, allowedPairs, mem_filter, mem_product,
    columnSupports, mem_powersetCard, subset_univ, true_and, binaryArrays, mem_univ, hcols, hcap]
  tauto

private theorem fromSupports_toSupports {n : ℕ} (a : BinaryArray n) :
    fromSupports (toSupports a) = a := by
  funext i c
  fin_cases c <;> simp [fromSupports, toSupports, supportOf]

private theorem toSupports_fromSupports {n : ℕ} (s : Supports n) :
    toSupports (fromSupports s) = s := by
  rcases s with ⟨K, A, B⟩
  have h₀ : supportOf (fromSupports ⟨K, A, B⟩) 0 = A := by
    ext i; simp [fromSupports, supportOf]
  have h₁ : supportOf (fromSupports ⟨K, A, B⟩) 1 = B := by
    ext i; simp [fromSupports, supportOf]
  have h₂ : supportOf (fromSupports ⟨K, A, B⟩) 2 = K := by
    ext i; simp [fromSupports, supportOf]
  simp [toSupports, h₀, h₁, h₂]

/-- The original binary-array count agrees with the column-subset count. -/
theorem binaryArrays_card_eq_supports (n k : ℕ) :
    (binaryArrays n k).card = (allowedTriples (α := Fin n) k).card := by
  refine card_bij (fun a _ => toSupports a) (fun a ha => (toSupports_mem_iff a).2 ha) ?_ ?_
  · intro a ha b hb heq
    change toSupports a = toSupports b at heq
    simpa only [fromSupports_toSupports] using congrArg fromSupports heq
  · intro s hs
    refine ⟨fromSupports s, (toSupports_mem_iff (fromSupports s)).1 ?_, toSupports_fromSupports s⟩
    simpa only [toSupports_fromSupports] using hs

/-- The original balanced-array polynomial, using binary matrices for its
coefficients. The coefficient is zero beyond k=n. -/
noncomputable def arrayRow (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n + 1), Polynomial.C ((binaryArrays n k).card : ℝ) * Polynomial.X ^ k

private theorem no_arrays_beyond {n k : ℕ} (hk : n < k) :
    binaryArrays n k = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro a ha
  rw [binaryArrays, mem_filter] at ha
  have hle := card_le_card (subset_univ (supportOf a 0))
  rw [ha.2.1 0, card_univ, Fintype.card_fin] at hle
  exact (Nat.not_le_of_lt hk) hle

/-- Every coefficient is the labeled binary-array count at its quota. -/
theorem coeff_arrayRow (n k : ℕ) :
    (arrayRow n).coeff k = ((binaryArrays n k).card : ℝ) := by
  classical
  simp only [arrayRow, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    sum_ite_eq, mem_range, Nat.lt_succ_iff]
  by_cases hk : k ≤ n
  · exact if_pos hk
  · rw [if_neg hk, no_arrays_beyond (Nat.lt_of_not_ge hk), card_empty, Nat.cast_zero]

/-- The original array polynomial equals the formula-verified polynomial. -/
theorem arrayRow_eq_originalRow (n : ℕ) :
    arrayRow n = BalancedThreeColumnPrefix.originalRow n := by
  simp only [arrayRow, BalancedThreeColumnPrefix.formulaRow, BalancedThreeColumnPrefix.rowCoeff,
    if_true]
  apply sum_congr rfl
  intro k _
  rw [binaryArrays_card_eq_supports]
  have h := allowedTriples_card (α := Fin n) k
  simp only [Fintype.card_fin] at h
  simpa only [Int.cast_natCast] using
    congrArg (fun z : ℤ => Polynomial.C (z : ℝ) * Polynomial.X ^ k) h

/-- The original array polynomial has degree ⌊2n/3⌋ in the finite prefix. -/
theorem array_prefix_natDegree {n : ℕ} (hn : n < 20) :
    (arrayRow n).natDegree = 2 * n / 3 := by
  rw [arrayRow_eq_originalRow]
  exact BalancedThreeColumnPrefix.formulaRow_natDegree_prefix true hn

/-- Every original array polynomial with at most nineteen rows has its full
degree of distinct negative roots. -/
theorem array_prefix_negative_roots {n : ℕ} (hn : n < 20) :
    ∃ roots : Fin (2 * n / 3) → ℝ, StrictMono roots ∧ (∀ i, 0 < roots i) ∧
      (arrayRow n).roots = (univ.image (fun i => -roots i)).val := by
  rw [arrayRow_eq_originalRow]
  exact BalancedThreeColumnPrefix.prefix_original_negative_roots hn

end Matrices

end BalancedThreeColumnCounting
