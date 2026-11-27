import ColorRelabel
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

private theorem card_support_size_fiber {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k m j : ℕ) (hk : k ≤ m) (hm : 0 < m) (hj : 0 < j) :
    Nat.card {s : SupportChoice A B a k // (s.val.1.card, s.val.2.card) = (m,j)} =
      (Fintype.card A - 1).choose (m - 1) * (Fintype.card B).choose j := by
  classical
  have e : {s : SupportChoice A B a k // (s.val.1.card, s.val.2.card) = (m,j)} ≃
      {S : Finset A // a ∈ S ∧ S.card = (m - 1) + 1} ×
      {T : Finset B // T.card = j} := by
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    refine {
      toFun := fun s => (⟨s.val.val.1, s.val.property.1, (congrArg Prod.fst s.property).trans hm'.symm⟩,
        ⟨s.val.val.2, congrArg Prod.snd s.property⟩)
      invFun := fun s => ⟨⟨(s.1.val, s.2.val), s.1.property.1,
        ((s.1.property.2.trans hm').symm ▸ hk), ?_⟩,
        Prod.ext (s.1.property.2.trans hm') s.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    apply card_pos.mp
    exact s.2.property.symm ▸ hj
  rw [Nat.card_congr e, Nat.card_prod, card_label_supports, card_color_supports]

private noncomputable def complFin {A : Type*} [Fintype A] (s : Finset A) :
    ((s : Set A)ᶜ : Set A) ≃ Fin (Fintype.card A - s.card) := by
  classical
  apply Fintype.equivFinOfCardEq
  letI : Fintype ((s : Set A) : Type _) := inferInstanceAs (Fintype (↑s : Type _))
  rw [Fintype.card_compl_set]
  change Fintype.card A - Fintype.card (↑s : Type _) = _
  rw [Fintype.card_coe]

noncomputable def taggedCount (n p k : ℕ) : ℕ := Nat.card (GoodPairs (Fin n) (Fin p) k)

private theorem card_residual {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset A) (T : Finset B) (k : ℕ) :
    Nat.card (Σ ρ : Equiv.Perm ((T : Set B)ᶜ : Set B),
      GoodWords (A := ((S : Set A)ᶜ : Set A)) ρ k) =
      taggedCount (Fintype.card A - S.card) (Fintype.card B - T.card) k :=
  Nat.card_congr ((pairsSigmaEquiv _ _ k).trans (goodPairsRelabel (complFin S) (complFin T) k))

/-- The exact tagged recurrence. The factorial for the anchored color cycle
is visible before normalizing by the total number of color permutations. -/
theorem taggedCount_succ (n p k : ℕ) (hk : 1 ≤ k) :
    taggedCount (n+1) p k =
      ∑ m ∈ Icc k (n+1), ∑ j ∈ Icc 1 p,
        (n.choose (m-1) * p.choose j) *
          (j ^ m * ((j-1).factorial * taggedCount (n+1-m) (p-j) k)) := by
  classical
  let a : Fin (n+1) := 0
  let sizes (s : SupportChoice (Fin (n+1)) (Fin p) a k) := (s.val.1.card, s.val.2.card)
  let D := (Icc k (n+1)).product (Icc 1 p)
  let term (q : ℕ × ℕ) :=
    q.2 ^ q.1 * ((q.2-1).factorial * taggedCount (n+1-q.1) (p-q.2) k)
  have hmap : ∀ s ∈ (univ : Finset (SupportChoice (Fin (n+1)) (Fin p) a k)), sizes s ∈ D := by
    intro s _
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨s.property.2.1, by simpa using card_le_univ s.val.1⟩,
      mem_Icc.mpr ⟨card_pos.mpr s.property.2.2, by simpa using card_le_univ s.val.2⟩⟩
  calc
    taggedCount (n+1) p k = ∑ s, term (sizes s) := by
      unfold taggedCount at *
      rw [card_goodPairs_support_sum a k]
      apply sum_congr rfl
      intro s _
      rw [card_residual, Fintype.card_fin, Fintype.card_fin]
    _ = ∑ q ∈ D, ∑ s ∈ univ.filter (fun s => sizes s = q), term (sizes s) :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ q ∈ D, (n.choose (q.1-1) * p.choose q.2) * term q := by
      apply sum_congr rfl
      intro q hq
      have hq' := (mem_product.mp hq)
      have h1 := (mem_Icc.mp hq'.1).1
      have h2 := (mem_Icc.mp hq'.2).1
      have hcard : (univ.filter fun s => sizes s = q).card =
          n.choose (q.1-1) * p.choose q.2 := by
        letI : Fintype {s : SupportChoice (Fin (n+1)) (Fin p) a k // sizes s = q} := Fintype.ofFinite _
        have he := card_support_size_fiber (B := Fin p) a k q.1 q.2 h1 (hk.trans h1) h2
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin, Fintype.card_fin,
          Nat.add_sub_cancel] at he
        exact he
      calc
        _ = ∑ _ ∈ univ.filter (fun s => sizes s = q), term q := by
          apply sum_congr rfl
          intro s hs
          rw [(mem_filter.mp hs).2]
        _ = _ := by simp [sum_const, nsmul_eq_mul, hcard]
    _ = _ := sum_product _ _ _

#print axioms taggedCount_succ
end OpenMathResearch.LongCycleExcedances.ColorAnchor
