import ColorPermSplit

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor

def GoodWords {A B : Type*} (π : Equiv.Perm B) (k : ℕ) :=
  {w : A → B // ∀ c, k ≤ load w π c}

def BlockWords {A B : Type*} (S : Set A) (T : Set B) (π : Equiv.Perm B) (k : ℕ) :=
  {w : {w : A → B // ∀ x, w x ∈ T ↔ x ∈ S} // ∀ c, k ≤ load w.val π c}

noncomputable def blockWordsEquiv {A B : Type*} (S : Set A) (T : Set B) (b : B) (hb : b ∈ T)
    (π : {π : Equiv.Perm B // OrbitSupport π T b}) (k : ℕ) (hS : k ≤ Nat.card S) :
    BlockWords S T π.val k ≃
      (S → T) × GoodWords (A := (Sᶜ : Set A)) (perm_at_support T b hb π).2 k := by
  obtain ⟨π, hπ⟩ := π
  have e : T = {y | π.SameCycle b y} :=
    Set.ext fun x => (hπ x).symm
  subst T
  have he : (perm_at_support _ b hb ⟨π, hπ⟩).2 = residualPerm π b := by
    ext x
    rfl
  change BlockWords S _ π k ≃ (S → _) × GoodWords (A := (Sᶜ : Set A))
    (perm_at_support _ b hb ⟨π, hπ⟩).2 k
  rw [he]
  exact (accepted_fixed_orbit_equiv S π b k hS).trans
    ((Equiv.refl _).prodCongr ((Equiv.refl _).subtypeEquiv (residualGood_iff S π b k)))

/-- For fixed support choices, split both the word and the varying color permutation.
The complement's word and permutation remain paired under exactly the same test. -/
noncomputable def accepted_at_supports {A B : Type*} (S : Set A) (T : Set B) (b : B)
    (hb : b ∈ T) (k : ℕ) (hS : k ≤ Nat.card S) :
    (Σ π : {π : Equiv.Perm B // OrbitSupport π T b}, BlockWords S T π.val k) ≃
    (S → T) × ({τ : Equiv.Perm T // Transitive τ} ×
      (Σ ρ : Equiv.Perm (Tᶜ : Set B), GoodWords (A := (Sᶜ : Set A)) ρ k)) := by
  let e := perm_at_support T b hb
  refine (Equiv.sigmaCongrRight (fun π => blockWordsEquiv S T b hb π k hS)).trans ?_
  let F (pair : {τ : Equiv.Perm T // Transitive τ} × Equiv.Perm (Tᶜ : Set B)) :=
    (S → T) × GoodWords (A := (Sᶜ : Set A)) pair.2 k
  have e' : (Σ π : {π : Equiv.Perm B // OrbitSupport π T b}, F (e π)) ≃
      (Σ pair, F pair) := Equiv.sigmaCongr e (fun _ => Equiv.refl _)
  refine e'.trans ?_
  exact {
    toFun := fun x => (x.2.1, x.1.1, ⟨x.1.2, x.2.2⟩)
    invFun := fun x => ⟨(x.2.1, x.2.2.1), (x.1, x.2.2.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

#print axioms accepted_at_supports
end OpenMathResearch.LongCycleExcedances.ColorAnchor
