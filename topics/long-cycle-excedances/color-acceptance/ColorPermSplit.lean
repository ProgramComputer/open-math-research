import ColorAnchor
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false

namespace OpenMathResearch.LongCycleExcedances.ColorAnchor

def OrbitSupport {B : Type*} (π : Equiv.Perm B) (T : Set B) (b : B) : Prop :=
  ∀ x, π.SameCycle b x ↔ x ∈ T

def Transitive {T : Type*} (π : Equiv.Perm T) : Prop :=
  ∀ x y, π.SameCycle x y

private theorem support_invariant {B : Type*} {π : Equiv.Perm B} {T : Set B} {b : B}
    (h : OrbitSupport π T b) (x : B) : x ∈ T ↔ π x ∈ T :=
  (h x).symm.trans (Equiv.Perm.sameCycle_apply_right.symm.trans (h (π x)))

private theorem support_of_transitive {B : Type*} {π : Equiv.Perm B} {T : Set B}
    {b : B} (hb : b ∈ T) (hinv : ∀ x, x ∈ T ↔ π x ∈ T)
    (ht : Transitive (π.subtypePerm (fun x => (hinv x).symm))) : OrbitSupport π T b := by
  intro x
  constructor
  · rintro ⟨j, rfl⟩
    let y := ((π.subtypePerm (fun x => (hinv x).symm)) ^ j) ⟨b, hb⟩
    simpa only [y, Equiv.Perm.subtypePerm_zpow, Equiv.Perm.subtypePerm_apply] using y.property
  · intro hx
    exact Equiv.Perm.sameCycle_subtypePerm.mp (ht ⟨b, hb⟩ ⟨x, hx⟩)

/-- Fixing the support of the distinguished color orbit leaves independent
permutations of that support and its complement. The support permutation is
transitive, including when the support consists of one fixed color. -/
noncomputable def perm_at_support {B : Type*} (T : Set B) (b : B) (hb : b ∈ T) :
    {π : Equiv.Perm B // OrbitSupport π T b} ≃
      {τ : Equiv.Perm T // Transitive τ} × Equiv.Perm (Tᶜ : Set B) := by
  classical
  let left (π : {π : Equiv.Perm B // OrbitSupport π T b}) : Equiv.Perm T :=
    π.val.subtypePerm (fun x => (support_invariant π.property x).symm)
  let join (pair : {τ : Equiv.Perm T // Transitive τ} × Equiv.Perm (Tᶜ : Set B)) :=
    (Equiv.Set.compl pair.1.val).symm pair.2
  let joined (pair : {τ : Equiv.Perm T // Transitive τ} × Equiv.Perm (Tᶜ : Set B)) :
      {π : Equiv.Perm B // OrbitSupport π T b} := by
    refine ⟨(join pair).val, ?_⟩
    have hmem (x : B) : x ∈ T ↔ (join pair).val x ∈ T := by
        constructor
        · intro hx
          rw [(join pair).property ⟨x, hx⟩]
          exact (pair.1.val ⟨x, hx⟩).property
        · intro hx
          let y := pair.1.val.symm ⟨(join pair).val x, hx⟩
          have he : (join pair).val y = (join pair).val x := by
            rw [(join pair).property y]
            exact congrArg Subtype.val (pair.1.val.apply_symm_apply _)
          exact ((join pair).val.injective he) ▸ y.property
    have hr : Equiv.Perm.subtypePerm (join pair).val (fun x => (hmem x).symm) = pair.1.val := by
      ext x
      exact (join pair).property x
    exact support_of_transitive hb hmem (hr.symm ▸ pair.1.property)
  refine {
    toFun := fun π =>
      (⟨left π, fun x y => Equiv.Perm.sameCycle_subtypePerm.mpr
        (((π.property x).mpr x.property).symm.trans ((π.property y).mpr y.property))⟩,
        Equiv.Set.compl (left π) ⟨π.val, fun _ => rfl⟩)
    invFun := joined
    left_inv := ?_
    right_inv := ?_ }
  · intro π
    apply Subtype.ext
    change ((Equiv.Set.compl (left π)).symm
      (Equiv.Set.compl (left π) ⟨π.val, fun _ => rfl⟩)).val = π.val
    rw [Equiv.symm_apply_apply]
  · intro pair
    have he : left (joined pair) = pair.1.val := by
      ext x
      exact (join pair).property x
    apply Prod.ext
    · exact Subtype.ext he
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      change (join pair).val x = (pair.2 x).val
      have h := (Equiv.Set.compl pair.1.val).apply_symm_apply pair.2
      exact congrArg (fun e : Equiv.Perm (Tᶜ : Set B) => (e x).val) h

#print axioms perm_at_support
end OpenMathResearch.LongCycleExcedances.ColorAnchor
