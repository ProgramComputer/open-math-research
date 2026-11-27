import ColorDoubleCount

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

private theorem permCongr_pow_apply {B B' : Type*} (e : B ≃ B') (π : Equiv.Perm B)
    (j : ℕ) (x : B) : (e.permCongr π ^ j) (e x) = e ((π ^ j) x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.permCongr_apply, Equiv.symm_apply_apply]

private theorem sameCycle_relabel {B B' : Type*} [Finite B] [Finite B']
    (e : B ≃ B') (π : Equiv.Perm B) (x y : B) :
    (e.permCongr π).SameCycle (e x) (e y) ↔ π.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    rw [permCongr_pow_apply] at hj
    exact ⟨(j : ℤ), by rw [zpow_natCast]; exact e.injective hj⟩
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    exact ⟨(j : ℤ), by rw [zpow_natCast, permCongr_pow_apply, hj]⟩

/-- The acceptance calculation depends only on the two ambient cardinalities. -/
def goodPairsRelabel {A A' B B' : Type*} [Finite B] [Finite B']
    (eA : A ≃ A') (eB : B ≃ B') (k : ℕ) : GoodPairs A B k ≃ GoodPairs A' B' k := by
  let e := (Equiv.arrowCongr eA eB).prodCongr eB.permCongr
  refine e.subtypeEquiv ?_
  intro pair
  have h (c : B) : load pair.1 pair.2 c = load (e pair).1 (e pair).2 (eB c) := by
    apply Nat.card_congr
    refine eA.subtypeEquiv fun x => ?_
    change pair.2.SameCycle c (pair.1 x) ↔
      (eB.permCongr pair.2).SameCycle (eB c) (eB (pair.1 (eA.symm (eA x))))
    rw [eA.symm_apply_apply, sameCycle_relabel]
  constructor
  · intro hp c
    obtain ⟨d, rfl⟩ := eB.surjective c
    rw [← h]
    exact hp d
  · intro hp c
    rw [h]
    exact hp (eB c)

def pairsSigmaEquiv (A B : Type*) (k : ℕ) :
    (Σ ρ : Equiv.Perm B, GoodWords (A := A) ρ k) ≃ GoodPairs A B k where
  toFun x := ⟨(x.2.val, x.1), x.2.property⟩
  invFun x := ⟨x.val.2, ⟨x.val.1, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

#print axioms goodPairsRelabel
end OpenMathResearch.LongCycleExcedances.ColorAnchor
