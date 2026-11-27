import ColorPermSplit
import Mathlib.GroupTheory.Perm.Centralizer

set_option autoImplicit false

namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Equiv.Perm

private theorem transitive_iff_cycleType_full {T : Type*} [Fintype T] [DecidableEq T]
    [Nontrivial T] (π : Equiv.Perm T) :
    Transitive π ↔ π.cycleType = {Fintype.card T} := by
  constructor
  · intro h
    have hnf (x : T) : π x ≠ x := by
      obtain ⟨y, hy⟩ := exists_ne x
      intro hx
      obtain ⟨j, hj⟩ := h x y
      rw [zpow_apply_eq_self_of_apply_eq_self hx] at hj
      exact hy hj.symm
    obtain ⟨x, _⟩ := exists_pair_ne T
    have hc : π.IsCycle := ⟨x, hnf x, fun {_} _ => h x _⟩
    have hfull : π.support = Finset.univ := Finset.eq_univ_of_forall fun x => mem_support.mpr (hnf x)
    rw [hc.cycleType, hfull, Finset.card_univ]
  · intro h x y
    have hc : π.IsCycle := card_cycleType_eq_one.mp (by simp [h])
    have hcard : π.support.card = Fintype.card T := by
      rw [← sum_cycleType, h, Multiset.sum_singleton]
    have hfull : π.support = Finset.univ := (Finset.card_eq_iff_eq_univ _).mp hcard
    obtain ⟨b, _, hb⟩ := hc
    have hs (x : T) : π x ≠ x := mem_support.mp (by rw [hfull]; exact Finset.mem_univ _)
    exact (hb (hs x)).symm.trans (hb (hs y))

/-- Transitive permutations of a nonempty finite set, including the identity
on a singleton. -/
theorem card_transitive_perms {T : Type*} [Fintype T] [Nonempty T] :
    Nat.card {π : Equiv.Perm T // Transitive π} = (Fintype.card T - 1).factorial := by
  classical
  rcases subsingleton_or_nontrivial T with hs | hn
  · letI : Subsingleton T := hs
    letI : Unique T := ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
    letI : Unique {π : Equiv.Perm T // Transitive π} :=
      ⟨⟨⟨1, fun x y => (Subsingleton.elim x y) ▸ SameCycle.refl 1 x⟩⟩,
       fun _ => Subtype.ext (Equiv.ext fun _ => Subsingleton.elim _ _)⟩
    simp [Nat.card_eq_fintype_card, Fintype.card_unique]
  · letI : Nontrivial T := hn
    letI : Fintype {π : Equiv.Perm T // π.cycleType = {Fintype.card T}} := Fintype.ofFinite _
    rw [Nat.card_congr (Equiv.subtypeEquiv (q := fun (π : Equiv.Perm T) => π.cycleType = {Fintype.card T}) (Equiv.refl _) transitive_iff_cycleType_full),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hc : 2 ≤ Fintype.card T := Fintype.one_lt_card
    rw [card_of_cycleType_singleton hc le_rfl, Nat.choose_self, mul_one]

#print axioms card_transitive_perms
end OpenMathResearch.LongCycleExcedances.ColorAnchor
