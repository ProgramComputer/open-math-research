import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Subtype

set_option autoImplicit false

namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

/-- The true orbit load at a color, including fixed colors of the color permutation. -/
noncomputable def load {A B : Type*} (w : A → B) (π : Equiv.Perm B) (c : B) : ℕ :=
  Nat.card {x : A // π.SameCycle c (w x)}

def Accepted (n p k : ℕ) :=
  { pair : (Fin n → Fin p) × Equiv.Perm (Fin p) //
    ∀ c, k ≤ load pair.1 pair.2 c }

noncomputable instance (n p k : ℕ) : Fintype (Accepted n p k) :=
  by unfold Accepted; exact Fintype.ofFinite _

private theorem sameCycle_iff_bounded {p : ℕ} (π : Equiv.Perm (Fin p)) (c d : Fin p) :
    π.SameCycle c d ↔ ∃ j : Fin p.factorial, (π ^ (j : ℕ)) c = d := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := h.exists_pow_eq'
    have hcard : orderOf π ≤ p.factorial := by
      apply Nat.le_of_dvd (Nat.factorial_pos p)
      simpa only [Fintype.card_perm, Fintype.card_fin] using orderOf_dvd_card (x := π)
    exact ⟨⟨j, hj.trans_le hcard⟩, he⟩
  · rintro ⟨j, hj⟩
    exact ⟨(j.val : ℤ), by simpa only [zpow_natCast] using hj⟩

/-- Executable finite orbit-load test, sufficient for defining the accepted finset. -/
def boundedLoad {n p : ℕ} (w : Fin n → Fin p) (π : Equiv.Perm (Fin p)) (c : Fin p) : ℕ :=
  (univ.filter fun x => ∃ j : Fin p.factorial, (π ^ (j : ℕ)) c = w x).card

theorem boundedLoad_eq_load {n p : ℕ} (w : Fin n → Fin p)
    (π : Equiv.Perm (Fin p)) (c : Fin p) : boundedLoad w π c = load w π c := by
  let s : Finset (Fin n) :=
    univ.filter fun x => ∃ j : Fin p.factorial, (π ^ (j : ℕ)) c = w x
  have e : (↑s : Type) ≃ {x : Fin n // π.SameCycle c (w x)} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun x => by
      simpa only [s, mem_filter, mem_univ, true_and, Equiv.refl_apply] using
        (sameCycle_iff_bounded π c (w x)).symm
  change s.card = load w π c
  rw [← Fintype.card_coe s, load, ← Nat.card_congr e, Nat.card_eq_fintype_card]

def acceptedFinset (n p k : ℕ) : Finset ((Fin n → Fin p) × Equiv.Perm (Fin p)) :=
  univ.filter fun pair => ∀ c, k ≤ boundedLoad pair.1 pair.2 c

theorem mem_acceptedFinset {n p k : ℕ} (pair : (Fin n → Fin p) × Equiv.Perm (Fin p)) :
    pair ∈ acceptedFinset n p k ↔ ∀ c, k ≤ load pair.1 pair.2 c := by
  simp only [acceptedFinset, mem_filter, mem_univ, true_and, boundedLoad_eq_load]

/-- Fixed pieces for a choice of a color subset and its exact preimage. -/
noncomputable def splitWords {A B : Type*} (S : Set A) (T : Set B) :
    {w : A → B // ∀ x, w x ∈ T ↔ x ∈ S} ≃
      (S → T) × ((Sᶜ : Set A) → (Tᶜ : Set B)) := by
  classical
  refine {
    toFun := fun w =>
      (fun x => ⟨w.val x.val, (w.property x.val).mpr x.property⟩,
       fun x => ⟨w.val x.val, fun h => x.property ((w.property x.val).mp h)⟩)
    invFun := fun f =>
      ⟨fun x => if h : x ∈ S then (f.1 ⟨x,h⟩).val else (f.2 ⟨x,h⟩).val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    dsimp only
    by_cases hx : x ∈ S
    · rw [dif_pos hx]
      exact ⟨fun _ => hx, fun _ => (f.1 ⟨x,hx⟩).property⟩
    · rw [dif_neg hx]
      exact ⟨fun h => ((f.2 ⟨x,hx⟩).property h).elim, fun h => (hx h).elim⟩
  · intro w
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  · intro f
    apply Prod.ext
    · funext x
      apply Subtype.ext
      simp [x.property]
    · funext x
      apply Subtype.ext
      have hx : x.val ∉ S := x.property
      simp [hx]

/-- With the two subsets fixed the number of unrestricted label assignments factors. -/
theorem card_splitWords {A B : Type*} [Finite A] [Finite B] (S : Set A) (T : Set B) :
    Nat.card {w : A → B // ∀ x, w x ∈ T ↔ x ∈ S} =
      Nat.card T ^ Nat.card S * Nat.card (Tᶜ : Set B) ^ Nat.card (Sᶜ : Set A) := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  letI : Fintype (Sᶜ : Set A) := Fintype.ofFinite _
  letI : Fintype (Tᶜ : Set B) := Fintype.ofFinite _
  rw [Nat.card_congr (splitWords S T)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun]

/-- Restrict a word to labels outside the distinguished orbit, retaining
the orbit relation of the original color permutation. -/
def ResidualGood {A B : Type*} (S : Set A) (T : Set B) (π : Equiv.Perm B)
    (k : ℕ) (w : (Sᶜ : Set A) → (Tᶜ : Set B)) : Prop :=
  ∀ c : (Tᶜ : Set B), k ≤ Nat.card {x : (Sᶜ : Set A) // π.SameCycle c.val (w x).val}

private theorem anchor_load {A B : Type*} (S : Set A) (π : Equiv.Perm B)
    (b : B) (w : {w : A → B // ∀ x, π.SameCycle b (w x) ↔ x ∈ S})
    {c : B} (hc : π.SameCycle b c) : load w.val π c = Nat.card S :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl A) fun x =>
    ⟨fun h => (w.property x).mp (hc.trans h),
     fun h => hc.symm.trans ((w.property x).mpr h)⟩)

private theorem outside_load {A B : Type*} (S : Set A) (π : Equiv.Perm B) (b : B)
    (w : {w : A → B // ∀ x, π.SameCycle b (w x) ↔ x ∈ S})
    (c : ({y : B | π.SameCycle b y}ᶜ : Set B)) :
    load w.val π c.val =
      Nat.card {x : (Sᶜ : Set A) // π.SameCycle c.val
        (((splitWords S {y : B | π.SameCycle b y}) w).2 x).val} := by
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨⟨x.val, fun hx =>
      c.property (((w.property x.val).mpr hx).trans x.property.symm)⟩, x.property⟩
    invFun := fun x => ⟨x.val.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The actual acceptance test factors on the labels in one fixed color orbit.
The anchor must have at least k labels. Their assignments inside that orbit
are unrestricted, and the complementary assignments obey the residual test. -/
noncomputable def accepted_fixed_orbit_equiv {A B : Type*} (S : Set A)
    (π : Equiv.Perm B) (b : B) (k : ℕ) (hS : k ≤ Nat.card S) :
    {w : {w : A → B // ∀ x, π.SameCycle b (w x) ↔ x ∈ S} //
        ∀ c, k ≤ load w.val π c} ≃
      (S → ({y : B | π.SameCycle b y} : Set B)) ×
      {w // ResidualGood S {y : B | π.SameCycle b y} π k w} := by
  classical
  let T : Set B := {y | π.SameCycle b y}
  have h : ∀ w : {w : A → B // ∀ x, π.SameCycle b (w x) ↔ x ∈ S},
      (∀ c, k ≤ load w.val π c) ↔ ResidualGood S T π k ((splitWords S T) w).2 := by
    intro w
    constructor
    · intro h c
      rw [← outside_load S π b w c]
      exact h c.val
    · intro h c
      by_cases hc : π.SameCycle b c
      · rw [anchor_load S π b w hc]
        exact hS
      · rw [outside_load S π b w ⟨c, hc⟩]
        exact h ⟨c, hc⟩
  let e : {w : {w : A → B // ∀ x, w x ∈ T ↔ x ∈ S} // ∀ c, k ≤ load w.val π c} ≃
      {f : (S → T) × ((Sᶜ : Set A) → (Tᶜ : Set B)) // ResidualGood S T π k f.2} :=
    Equiv.subtypeEquiv (splitWords S T) h
  refine e.trans ?_
  exact {
    toFun := fun f => (f.val.1, ⟨f.val.2, f.property⟩)
    invFun := fun f => ⟨(f.1, f.2.val), f.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Restrict the actual color permutation to the complement of its anchored orbit. -/
def residualPerm {B : Type*} (π : Equiv.Perm B) (b : B) :
    Equiv.Perm ({y : B | π.SameCycle b y}ᶜ : Set B) :=
  π.subtypePerm (fun _ => not_congr Equiv.Perm.sameCycle_apply_right.symm)

/-- The restriction to the anchored orbit is transitive even for a singleton
color. Using IsCycle would incorrectly exclude this case. -/
def anchoredPerm {B : Type*} (π : Equiv.Perm B) (b : B) :
    Equiv.Perm ({y : B | π.SameCycle b y} : Set B) :=
  π.subtypePerm (fun _ => Equiv.Perm.sameCycle_apply_right.symm)

theorem anchoredPerm_transitive {B : Type*} (π : Equiv.Perm B) (b : B)
    (c d : ({y : B | π.SameCycle b y} : Set B)) :
    (anchoredPerm π b).SameCycle c d :=
  Equiv.Perm.sameCycle_subtypePerm.mpr (c.property.symm.trans d.property)

theorem residualGood_iff {A B : Type*} (S : Set A) (π : Equiv.Perm B) (b : B) (k : ℕ)
    (w : (Sᶜ : Set A) → ({y : B | π.SameCycle b y}ᶜ : Set B)) :
    ResidualGood S {y : B | π.SameCycle b y} π k w ↔
      ∀ c, k ≤ load w (residualPerm π b) c := by
  have he (c : ({y : B | π.SameCycle b y}ᶜ : Set B)) :
      load w (residualPerm π b) c =
        Nat.card {x : (Sᶜ : Set A) // π.SameCycle c.val (w x).val} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun _ =>
      Equiv.Perm.sameCycle_subtypePerm)
  simp only [ResidualGood, he]

theorem card_accepted_fixed_orbit {A B : Type*} [Finite A] [Finite B] (S : Set A)
    (π : Equiv.Perm B) (b : B) (k : ℕ) (hS : k ≤ Nat.card S) :
    Nat.card {w : {w : A → B // ∀ x, π.SameCycle b (w x) ↔ x ∈ S} //
        ∀ c, k ≤ load w.val π c} =
      Nat.card ({y : B | π.SameCycle b y} : Set B) ^ Nat.card S *
      Nat.card {w : (Sᶜ : Set A) → ({y : B | π.SameCycle b y}ᶜ : Set B) //
        ∀ c, k ≤ load w (residualPerm π b) c} := by
  classical
  let T : Set B := {y | π.SameCycle b y}
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype T := Fintype.ofFinite _
  let e := Equiv.subtypeEquiv
    (q := fun w : (Sᶜ : Set A) → (Tᶜ : Set B) => ∀ c, k ≤ load w (residualPerm π b) c)
    (Equiv.refl ((Sᶜ : Set A) → (Tᶜ : Set B))) (residualGood_iff S π b k)
  rw [Nat.card_congr ((accepted_fixed_orbit_equiv S π b k hS).trans
    ((Equiv.refl (S → T)).prodCongr e)), Nat.card_prod]
  congr 1
  change Nat.card (S → T) = Nat.card T ^ Nat.card S
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- The choices of the assigned label subset are recovered directly from a word. -/
noncomputable def partitionWordsAtAnchor {A B : Type*} (a : A) (T : Set B) :
    {w : A → B // w a ∈ T} ≃
      Σ S : {S : Set A // a ∈ S}, {w : A → B // ∀ x, w x ∈ T ↔ x ∈ S.val} where
  toFun w := ⟨⟨{x | w.val x ∈ T}, w.property⟩, ⟨w.val, fun _ => Iff.rfl⟩⟩
  invFun pair := ⟨pair.2.val, (pair.2.property a).mpr pair.1.property⟩
  left_inv _ := rfl
  right_inv := by
    intro ⟨S, w⟩
    have he : (⟨{x | w.val x ∈ T}, (w.property a).mpr S.property⟩ : {S : Set A // a ∈ S}) = S :=
      Subtype.ext (Set.ext w.property)
    apply Sigma.ext he
    have hset : {x | w.val x ∈ T} = S.val := Set.ext w.property
    have hp (f : A → B) : (∀ x, f x ∈ T ↔ x ∈ {y | w.val y ∈ T}) ↔
        (∀ x, f x ∈ T ↔ x ∈ S.val) := by rw [hset]
    exact (Subtype.heq_iff_coe_eq hp).2 rfl

#print axioms mem_acceptedFinset
#print axioms splitWords
#print axioms card_splitWords
#print axioms accepted_fixed_orbit_equiv
#print axioms residualGood_iff
#print axioms anchoredPerm_transitive
#print axioms card_accepted_fixed_orbit
#print axioms partitionWordsAtAnchor
#guard (acceptedFinset 0 0 2).card == 1
#guard (acceptedFinset 0 1 2).card == 0
#guard (acceptedFinset 3 2 2).card == 8

end OpenMathResearch.LongCycleExcedances.ColorAnchor
