import ColorBlock
import ColorCycleCount
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

theorem card_accepted_at_supports {A B : Type*} [Finite A] [Finite B]
    (S : Set A) (T : Set B) (b : B) (hb : b ∈ T) (k : ℕ) (hS : k ≤ Nat.card S) :
    Nat.card (Σ π : {π : Equiv.Perm B // OrbitSupport π T b}, BlockWords S T π.val k) =
      Nat.card T ^ Nat.card S * ((Nat.card T - 1).factorial *
        Nat.card (Σ ρ : Equiv.Perm (Tᶜ : Set B), GoodWords (A := (Sᶜ : Set A)) ρ k)) := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  letI : Nonempty T := ⟨⟨b, hb⟩⟩
  rw [Nat.card_congr (accepted_at_supports S T b hb k hS), Nat.card_prod, Nat.card_prod,
    card_transitive_perms]
  have h : Nat.card (S → T) = Nat.card T ^ Nat.card S := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [h, Nat.card_eq_fintype_card (α := T)]

theorem card_color_supports {B : Type*} [Fintype B] (j : ℕ) :
    Nat.card {T : Finset B // T.card = j} = (Fintype.card B).choose j := by
  classical
  have e : {T : Finset B // T.card = j} ≃ ↑(powersetCard j (univ : Finset B)) :=
    Equiv.subtypeEquiv (Equiv.refl _) fun T => by
      simp [mem_powersetCard]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_powersetCard, card_univ]

theorem card_label_supports {A : Type*} [Fintype A] (a : A) (m : ℕ) :
    Nat.card {S : Finset A // a ∈ S ∧ S.card = m + 1} =
      (Fintype.card A - 1).choose m := by
  classical
  let D := powersetCard m ((univ : Finset A).erase a)
  have e : {S : Finset A // a ∈ S ∧ S.card = m + 1} ≃ ↑D := by
    refine {
      toFun := fun S => ⟨S.val.erase a, ?_⟩
      invFun := fun R => ⟨insert a R.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · apply mem_powersetCard.mpr
      exact ⟨erase_subset_erase _ (subset_univ _), by
        rw [card_erase_of_mem S.property.1, S.property.2, Nat.add_sub_cancel]⟩
    · obtain ⟨hs, hc⟩ := mem_powersetCard.mp R.property
      have ha : a ∉ R.val := fun h => notMem_erase a _ (hs h)
      exact ⟨mem_insert_self _ _, by rw [card_insert_of_notMem ha, hc]⟩
    · intro S
      apply Subtype.ext
      exact insert_erase S.property.1
    · intro R
      apply Subtype.ext
      have hs := (mem_powersetCard.mp R.property).1
      exact erase_insert (fun h => notMem_erase a _ (hs h))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_powersetCard,
    card_erase_of_mem (mem_univ _), card_univ]

#print axioms card_accepted_at_supports
#print axioms card_color_supports
#print axioms card_label_supports
end OpenMathResearch.LongCycleExcedances.ColorAnchor
