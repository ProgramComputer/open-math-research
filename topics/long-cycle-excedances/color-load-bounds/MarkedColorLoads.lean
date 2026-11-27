import ColorSupportCount
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset
abbrev SizeSupport (n j : ℕ) := {T : Finset (Fin n) // T.card=j}

private def supportRep {p j : ℕ} (T : SizeSupport p j) (hj : 0 < j) : Fin p :=
  Classical.choose (Finset.card_pos.mp (by rw [T.property]; exact hj : 0 < T.val.card))

private theorem supportRep_mem {p j : ℕ} (T : SizeSupport p j) (hj : 0 < j) :
    supportRep T hj ∈ T.val :=
  Classical.choose_spec (Finset.card_pos.mp (by rw [T.property]; exact hj : 0 < T.val.card))

/-- An actual permutation with one marked j-color orbit, together with a word
placing exactly i labels on that orbit. Supports name the orbit only once. -/
def MarkedColorLoad (n p i j : ℕ) (hj : 0 < j) :=
  Σ T : SizeSupport p j, Σ S : SizeSupport n i,
    {π : Equiv.Perm (Fin p) // OrbitSupport π (T.val : Set (Fin p)) (supportRep T hj)} ×
    {w : Fin n → Fin p // ∀ x, w x ∈ (T.val : Set (Fin p)) ↔ x ∈ (S.val : Set (Fin n))}

private theorem support_compl {n i : ℕ} (s : SizeSupport n i) :
    Nat.card ((s.val : Set (Fin n))ᶜ : Set (Fin n))=n-i := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_compl_set]
  simp [s.property]

theorem marked_color_load_card (n p i j : ℕ) (hj : 0 < j) :
    Nat.card (MarkedColorLoad n p i j hj) =
    p.choose j*(n.choose i)*((j-1).factorial*(p-j).factorial)*
      (j^i*(p-j)^(n-i)) := by
  classical
  letI : Fintype (SizeSupport p j) := Fintype.ofFinite _
  letI : Fintype (SizeSupport n i) := Fintype.ofFinite _
  have eq (T : SizeSupport p j) (S : SizeSupport n i) :
      Nat.card ({π : Equiv.Perm (Fin p) // OrbitSupport π (T.val : Set (Fin p)) (supportRep T hj)} ×
      {w : Fin n → Fin p // ∀ x, w x ∈ (T.val : Set (Fin p)) ↔ x ∈ (S.val : Set (Fin n))}) =
      ((j-1).factorial*(p-j).factorial)*(j^i*(p-j)^(n-i)) := by
    letI : Nonempty ((T.val : Set (Fin p)) : Type _) := ⟨⟨supportRep T hj,supportRep_mem T hj⟩⟩
    rw [Nat.card_prod,Nat.card_congr (perm_at_support (T.val : Set (Fin p)) _ (supportRep_mem T hj)),
      Nat.card_prod,card_transitive_perms,card_splitWords (S.val : Set (Fin n)) (T.val : Set (Fin p))]
    have cT : Nat.card ((T.val : Set (Fin p)) : Type _)=j := by simp [T.property]
    have cS : Nat.card ((S.val : Set (Fin n)) : Type _)=i := by simp [S.property]
    rw [←Nat.card_eq_fintype_card,cT,cS,support_compl T,support_compl S]
    have cc : Nat.card (Equiv.Perm (↑((T.val : Set (Fin p))ᶜ))) = (p-j).factorial := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm,←Nat.card_eq_fintype_card,support_compl T]
    rw [cc]
  unfold MarkedColorLoad
  rw [Nat.card_sigma]
  simp only [Nat.card_sigma,eq,sum_const,card_univ,smul_eq_mul]
  have hp : Fintype.card (SizeSupport p j)=p.choose j := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using (card_color_supports (B:=Fin p) j)
  have hn : Fintype.card (SizeSupport n i)=n.choose i := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using (card_color_supports (B:=Fin n) i)
  rw [hp,hn]; ring

/-- One exceptional orbit exists in the actual product sample space. -/
def ExceptionalPairs (n p : ℕ) (bad : ℕ → ℕ → Prop) :=
  {ω : (Fin n → Fin p) × Equiv.Perm (Fin p) //
    ∃ c : Fin p, bad (Nat.card {x : Fin p // ω.2.SameCycle c x}) (load ω.1 ω.2 c)}

def MarkedExceptions (n p : ℕ) (bad : ℕ → ℕ → Prop) :=
  Σ j : {j : Fin (p+1) // 0 < j.val},
    Σ i : {i : Fin (n+1) // bad j.val.val i.val}, MarkedColorLoad n p i.val.val j.val.val j.property

/-- First-moment comparison. Choose one exceptional orbit and recover
the original word and permutation by forgetting the mark. -/
theorem exceptional_color_pairs_le_marks (n p : ℕ) (bad : ℕ → ℕ → Prop) :
    Nat.card (ExceptionalPairs n p bad) ≤ Nat.card (MarkedExceptions n p bad) := by
  classical
  let mark (ω : ExceptionalPairs n p bad) : MarkedExceptions n p bad := by
    let w := ω.val.1
    let π := ω.val.2
    let c := Classical.choose ω.property
    let T := (univ : Finset (Fin p)).filter (π.SameCycle c)
    let S := (univ : Finset (Fin n)).filter (fun x => π.SameCycle c (w x))
    have hc : c∈T := by simp [T,Equiv.Perm.SameCycle.refl]
    have eqT : T.card=Nat.card {x : Fin p // π.SameCycle c x} := by
      change (univ.filter _).card=_
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have eqS : S.card=load w π c := by
      unfold load
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have hbad : bad T.card S.card := by
      rw [eqT,eqS]; exact Classical.choose_spec ω.property
    let j : {j : Fin (p+1) // 0 < j.val} := ⟨⟨T.card,by
      have h := card_le_univ T; simp only [Fintype.card_fin] at h; omega⟩,card_pos.mpr ⟨c,hc⟩⟩
    let i : {i : Fin (n+1) // bad j.val.val i.val} := ⟨⟨S.card,by
      have h := card_le_univ S; simp only [Fintype.card_fin] at h; omega⟩,hbad⟩
    let tt : SizeSupport p j.val.val := ⟨T,rfl⟩
    let ss : SizeSupport n i.val.val := ⟨S,rfl⟩
    refine ⟨j,i,tt,ss,⟨π,?_⟩,⟨w,?_⟩⟩
    · have hc' := supportRep_mem tt j.property
      have same : π.SameCycle c (supportRep tt j.property) := (mem_filter.mp hc').2
      intro x
      change π.SameCycle _ x ↔ x∈T
      simp only [T,mem_filter,mem_univ,true_and]
      exact ⟨fun h => same.trans h, fun h => same.symm.trans h⟩
    · intro x; change w x∈T ↔ x∈S
      simp [T,S]
  let forget (z : MarkedExceptions n p bad) : (Fin n → Fin p) × Equiv.Perm (Fin p) :=
    (z.2.2.2.2.2.val,z.2.2.2.2.1.val)
  letI : Finite (MarkedExceptions n p bad) := by unfold MarkedExceptions MarkedColorLoad; infer_instance
  apply Nat.card_le_card_of_injective mark
  intro u v h; exact Subtype.ext (congrArg forget h)

private theorem compare_two_events {A : Type*} [Finite A] (P Q R : A → Prop)
    (hr : ∀ x, P x → ¬Q x → R x) :
    Nat.card {x // P x} ≤ Nat.card {x // Q x} + Nat.card {x // R x} := by
  classical
  let encode (x : {x // P x}) : {x // Q x} ⊕ {x // R x} :=
    if h : Q x.val then Sum.inl ⟨x.val,h⟩ else Sum.inr ⟨x.val,hr _ x.property h⟩
  let forget : {x // Q x} ⊕ {x // R x} → A := Sum.elim Subtype.val Subtype.val
  have forget_encode (x : {x // P x}) : forget (encode x) = x.val := by
    simp only [encode]; split <;> rfl
  rw [←Nat.card_sum]
  apply Nat.card_le_card_of_injective encode
  intro a b h
  exact Subtype.ext ((forget_encode a).symm.trans ((congrArg forget h).trans (forget_encode b)))

def orbitSize {p : ℕ} (π : Equiv.Perm (Fin p)) (c : Fin p) :=
  Nat.card {x : Fin p // π.SameCycle c x}

/-- All color cycles have at least b colors. The independent word is free. -/
def BaselinePairs (n p b : ℕ) :=
  {ω : (Fin n → Fin p) × Equiv.Perm (Fin p) // ∀ c, b ≤ orbitSize ω.2 c}

/-- Two-sided comparison between the size cutoff on color cycles and the
load cutoff on the original words. A single exceptional marked orbit
accounts for every pair belonging to just one of the two events. -/
theorem color_load_cutoff_comparison (n p k b : ℕ) :
    Nat.card (BaselinePairs n p b) ≤ Nat.card (Accepted n p k) +
      Nat.card (MarkedExceptions n p (fun j i => b ≤ j ∧ i < k)) ∧
    Nat.card (Accepted n p k) ≤ Nat.card (BaselinePairs n p b) +
      Nat.card (MarkedExceptions n p (fun j i => j < b ∧ k ≤ i)) := by
  let P (ω : (Fin n → Fin p) × Equiv.Perm (Fin p)) := ∀ c, b ≤ orbitSize ω.2 c
  let Q (ω : (Fin n → Fin p) × Equiv.Perm (Fin p)) := ∀ c, k ≤ load ω.1 ω.2 c
  constructor
  · apply le_trans _ (Nat.add_le_add_left
      (exceptional_color_pairs_le_marks n p (fun j i => b ≤ j ∧ i < k)) _)
    apply compare_two_events P Q
    intro ω h hnot
    change ¬∀ c, k ≤ load ω.1 ω.2 c at hnot
    push_neg at hnot
    obtain ⟨c,hc⟩ := hnot
    exact ⟨c,h c,hc⟩
  · apply le_trans _ (Nat.add_le_add_left
      (exceptional_color_pairs_le_marks n p (fun j i => j < b ∧ k ≤ i)) _)
    apply compare_two_events Q P
    intro ω h hnot
    change ¬∀ c, b ≤ orbitSize ω.2 c at hnot
    push_neg at hnot
    obtain ⟨c,hc⟩ := hnot
    exact ⟨c,hc,h c⟩

#print axioms color_load_cutoff_comparison
#print axioms exceptional_color_pairs_le_marks
#print axioms marked_color_load_card
end OpenMathResearch.LongCycleExcedances.ColorAnchor
