import ColorSupportCount

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

def GoodPairs (A B : Type*) (k : ℕ) :=
  {pair : (A → B) × Equiv.Perm B // ∀ c, k ≤ load pair.1 pair.2 c}

def SupportChoice (A B : Type*) (a : A) (k : ℕ) :=
  {ST : Finset A × Finset B // a ∈ ST.1 ∧ k ≤ ST.1.card ∧ ST.2.Nonempty}

private noncomputable def supportOf {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k : ℕ) (x : GoodPairs A B k) : SupportChoice A B a k := by
  classical
  let b := x.val.1 a
  let T := (univ : Finset B).filter (x.val.2.SameCycle b)
  let S := (univ : Finset A).filter fun y => x.val.1 y ∈ T
  have hb : b ∈ T := by simp [T, Equiv.Perm.SameCycle.refl]
  have e : (↑S : Type _) ≃ {y : A // x.val.2.SameCycle b (x.val.1 y)} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun _ => by simp [S,T]
  have hc : S.card = load x.val.1 x.val.2 b := by
    rw [← Fintype.card_coe S, load, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact ⟨(S,T), by simp [S,hb,b], by rw [hc]; exact x.property b, ⟨b,hb⟩⟩

private noncomputable def representative {A B : Type*} {a : A} {k : ℕ}
    (s : SupportChoice A B a k) : B :=
  s.property.2.2.choose

private theorem representative_mem {A B : Type*} {a : A} {k : ℕ}
    (s : SupportChoice A B a k) : representative s ∈ s.val.2 :=
  s.property.2.2.choose_spec

private noncomputable def blockFiber {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k : ℕ) (s : SupportChoice A B a k) :
    {x : GoodPairs A B k // supportOf a k x = s} ≃
      (Σ π : {π : Equiv.Perm B // OrbitSupport π (s.val.2 : Set B) (representative s)},
        BlockWords (s.val.1 : Set A) (s.val.2 : Set B) π.val k) := by
  classical
  have toOrbit (x : GoodPairs A B k) (hx : supportOf a k x = s) :
      OrbitSupport x.val.2 (s.val.2 : Set B) (representative s) := by
    have ht : ∀ z, z ∈ s.val.2 ↔ x.val.2.SameCycle (x.val.1 a) z := by
      intro z
      rw [← hx]
      simp [supportOf]
    have hrep := (ht _).mp (representative_mem s)
    intro z
    exact ⟨fun hz => (ht _).mpr (hrep.trans hz), fun hz => hrep.symm.trans ((ht _).mp hz)⟩
  have toWord (x : GoodPairs A B k) (hx : supportOf a k x = s) :
      ∀ y, x.val.1 y ∈ (s.val.2 : Set B) ↔ y ∈ (s.val.1 : Set A) := by
    rw [← hx]
    intro y
    simp [supportOf]
  refine {
    toFun := fun x => ⟨⟨x.val.val.2, toOrbit x.val x.property⟩,
      ⟨⟨x.val.val.1, toWord x.val x.property⟩, x.val.property⟩⟩
    invFun := fun y => ⟨⟨(y.2.val.val, y.1.val), y.2.property⟩, ?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  apply Subtype.ext
  apply Prod.ext
  · ext z
    simp only [supportOf, mem_filter, mem_univ, true_and]
    have hb := (y.1.property _).mpr ((y.2.val.property a).mpr s.property.1)
    exact ⟨fun hz => (y.2.val.property z).mp ((y.1.property _).mp (hb.trans hz)),
      fun hz => hb.symm.trans ((y.1.property _).mpr ((y.2.val.property z).mpr hz))⟩
  · ext z
    simp only [supportOf, mem_filter, mem_univ, true_and]
    have hb := (y.1.property _).mpr ((y.2.val.property a).mpr s.property.1)
    exact ⟨fun hz => (y.1.property _).mp (hb.trans hz),
      fun hz => hb.symm.trans ((y.1.property _).mpr hz)⟩

/-- The exact disjoint union giving the anchored double count of actual pairs. -/
noncomputable def acceptedSupportDecomposition {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k : ℕ) : GoodPairs A B k ≃
    Σ s : SupportChoice A B a k,
      (↑s.val.1 → ↑s.val.2) ×
        ({τ : Equiv.Perm (↑s.val.2 : Type _) // Transitive τ} ×
         (Σ ρ : Equiv.Perm ((s.val.2 : Set B)ᶜ : Set B),
          GoodWords (A := ((s.val.1 : Set A)ᶜ : Set A)) ρ k)) := by
  refine (Equiv.sigmaFiberEquiv (supportOf a k)).symm.trans ?_
  apply Equiv.sigmaCongrRight
  intro s
  let S : Set A := s.val.1
  let T : Set B := s.val.2
  have hm : k ≤ Nat.card S := by
    change k ≤ Nat.card (↑s.val.1 : Type _)
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact s.property.2.1
  exact (blockFiber a k s).trans (accepted_at_supports S T (representative s)
    (representative_mem s) k hm)

noncomputable instance supportChoiceFintype {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k : ℕ) : Fintype (SupportChoice A B a k) := by
  unfold SupportChoice
  exact Fintype.ofFinite _

/-- The actual tagged count as an exact sum over distinguished label/color supports. -/
theorem card_goodPairs_support_sum {A B : Type*} [Fintype A] [Fintype B]
    (a : A) (k : ℕ) :
    Nat.card (GoodPairs A B k) =
      ∑ s : SupportChoice A B a k, s.val.2.card ^ s.val.1.card *
       ((s.val.2.card - 1).factorial *
        Nat.card (Σ ρ : Equiv.Perm ((s.val.2 : Set B)ᶜ : Set B),
          GoodWords (A := ((s.val.1 : Set A)ᶜ : Set A)) ρ k)) := by
  classical
  letI goodWordsFinite (s : SupportChoice A B a k)
      (ρ : Equiv.Perm ((s.val.2 : Set B)ᶜ : Set B)) :
      Finite (GoodWords (A := ((s.val.1 : Set A)ᶜ : Set A)) ρ k) := by
    unfold GoodWords
    infer_instance
  rw [Nat.card_congr (acceptedSupportDecomposition a k), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  letI : Nonempty (↑s.val.2 : Type _) := ⟨⟨representative s, representative_mem s⟩⟩
  rw [Nat.card_prod, Nat.card_prod, card_transitive_perms]
  simp only [Nat.card_eq_fintype_card (α := (↑s.val.1 → ↑s.val.2)),
      Nat.card_eq_fintype_card (α := (↑s.val.1 : Type _)),
      Nat.card_eq_fintype_card (α := (↑s.val.2 : Type _)), Fintype.card_fun, Fintype.card_coe]

#print axioms acceptedSupportDecomposition
#print axioms card_goodPairs_support_sum
end OpenMathResearch.LongCycleExcedances.ColorAnchor
