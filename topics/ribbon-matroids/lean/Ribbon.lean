import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-!
The polygon reduction in the ribbon proof. Vertices are `0, …, n - 1` in cyclic
order. Edges are stored as increasing pairs. The deletion theorem and the circuit
coefficient evaluation are explicit hypotheses, since this file does not build
the matroid Kazhdan–Lusztig or Z-polynomial theory.
-/

namespace Ribbon

abbrev Edge := Nat × Nat
abbrev Graph := Edge → Prop

def boundary (n : Nat) (e : Edge) : Prop :=
  e.2 < n ∧ (e.2 = e.1 + 1 ∨ (e.1 = 0 ∧ e.2 + 1 = n ∧ 0 < e.2))

def diagonal (n : Nat) (e : Edge) : Prop :=
  e.2 < n ∧ e.1 + 1 < e.2 ∧ ¬(e.1 = 0 ∧ e.2 + 1 = n)

def crosses (e f : Edge) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨
    (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

def polygon (n : Nat) (diagonals : Finset Edge) : Graph :=
  fun e => boundary n e ∨ e ∈ diagonals

def eraseEdge (G : Graph) (e : Edge) : Graph := fun f => G f ∧ f ≠ e

def fits (side : Nat → Prop) (e : Edge) : Prop := side e.1 ∧ side e.2

def restrictEdges (G : Graph) (side : Nat → Prop) : Graph := fun e => G e ∧ fits side e

inductive Reachable (G : Graph) : Nat → Nat → Prop
  | refl (v) : Reachable G v v
  | step {u v} : (G (u, v) ∨ G (v, u)) → Reachable G u v
  | trans {u v w} : Reachable G u v → Reachable G v w → Reachable G u w

theorem Reachable.symm {G : Graph} {v w : Nat} (h : Reachable G v w) : Reachable G w v := by
  induction h with
  | refl v => exact .refl v
  | step h => exact .step h.symm
  | trans _ _ h₁ h₂ => exact .trans h₂ h₁

theorem Reachable.mono {G H : Graph} {v w : Nat} (h : Reachable G v w)
    (subset : ∀ e, G e → H e) : Reachable H v w := by
  induction h with
  | refl v => exact .refl v
  | step h => exact .step (h.imp (subset _) (subset _))
  | trans _ _ h₁ h₂ => exact .trans h₁ h₂

theorem intervalReachable {G : Graph} {a b : Nat}
    (edges : ∀ v, a ≤ v → v < b → G (v, v + 1)) :
    ∀ v, a ≤ v → v ≤ b → Reachable G a v := by
  intro v
  induction v with
  | zero =>
    intro ha _
    have ah : a = 0 := by omega
    subst a
    exact .refl 0
  | succ v ih =>
    intro ha hb
    by_cases eq : a = v + 1
    · subst a
      exact .refl _
    · exact .trans (ih (by omega) (by omega)) (.step (.inl (edges v (by omega) (by omega))))

structure ParallelAlong (n : Nat) (G : Graph) (e : Edge) where
  ordered : ∀ f, G f → f.1 < f.2 ∧ f.2 < n
  edge : G e
  firstSide : Nat → Prop
  secondSide : Nat → Prop
  vertexCover : ∀ v < n, firstSide v ∨ secondSide v
  commonVertices : ∀ v, firstSide v ∧ secondSide v ↔ v = e.1 ∨ v = e.2
  edgeCover : ∀ f, G f → fits firstSide f ∨ fits secondSide f
  firstConnected : ∀ v, firstSide v → Reachable (restrictEdges (eraseEdge G e) firstSide) e.1 v
  secondConnected : ∀ v, secondSide v → Reachable (restrictEdges (eraseEdge G e) secondSide) e.1 v

theorem ParallelAlong.commonEdge {n : Nat} {G : Graph} {e f : Edge}
    (h : ParallelAlong n G e) (hf : G f) :
    fits h.firstSide f ∧ fits h.secondSide f ↔ f = e := by
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    have l := (h.commonVertices f.1).mp ⟨h₁, h₃⟩
    have r := (h.commonVertices f.2).mp ⟨h₂, h₄⟩
    have ho := (h.ordered f hf).1
    have he := (h.ordered e h.edge).1
    exact Prod.ext (by omega) (by omega)
  · intro eq
    subst f
    have l := (h.commonVertices e.1).mpr (.inl rfl)
    have r := (h.commonVertices e.2).mpr (.inr rfl)
    exact ⟨⟨l.1, r.1⟩, ⟨l.2, r.2⟩⟩

theorem ParallelAlong.endpointsAfterDeletion {n : Nat} {G : Graph} {e : Edge}
    (h : ParallelAlong n G e) : Reachable (eraseEdge G e) e.1 e.2 :=
  (h.firstConnected e.2 ((h.commonVertices e.2).mpr (.inr rfl)).1).mono
    (fun _ hf => hf.1)

theorem diagonal_not_boundary {n : Nat} {e : Edge} (he : diagonal n e) : ¬boundary n e := by
  simp only [diagonal, boundary] at *
  omega

def polygonParallel {n : Nat} {S : Finset Edge} {e : Edge} (he : e ∈ S)
    (hd : ∀ f ∈ S, diagonal n f)
    (hn : ∀ f ∈ S, ¬crosses e f) : ParallelAlong n (polygon n S) e := by
  let first : Nat → Prop := fun v => e.1 ≤ v ∧ v ≤ e.2
  let second : Nat → Prop := fun v => v < n ∧ (v ≤ e.1 ∨ e.2 ≤ v)
  have hedge := hd e he
  have eb : e.2 < n := hedge.1
  have en : e.1 + 1 < e.2 := hedge.2.1
  have hg : ∀ f, polygon n S f → f.1 < f.2 ∧ f.2 < n := by
    intro f hf
    rcases hf with hb | hm
    · unfold boundary at hb
      omega
    · have hh := hd f hm
      unfold diagonal at hh
      omega
  have noCross : ∀ f, polygon n S f → ¬crosses e f := by
    intro f hf
    rcases hf with hb | hm
    · unfold crosses boundary at *
      omega
    · exact hn f hm
  have firstArc : ∀ v, e.1 ≤ v → v < e.2 →
      restrictEdges (eraseEdge (polygon n S) e) first (v, v + 1) := by
    intro v h₁ h₂
    refine ⟨⟨Or.inl ⟨by omega, .inl rfl⟩, ?_⟩, ?_⟩
    · intro h
      have h' := congrArg Prod.fst h
      have h'' := congrArg Prod.snd h
      dsimp at h' h''
      omega
    · simp only [fits, first]
      omega
  let outer := restrictEdges (eraseEdge (polygon n S) e) second
  have oddge : ∀ v, v + 1 < n → (v + 1 ≤ e.1 ∨ e.2 ≤ v) → outer (v, v + 1) := by
    intro v hn' hs
    refine ⟨⟨Or.inl ⟨hn', .inl rfl⟩, ?_⟩, ?_⟩
    · intro h
      have h' := congrArg Prod.fst h
      have h'' := congrArg Prod.snd h
      dsimp at h' h''
      omega
    · simp only [fits, second]
      omega
  have leftWalk : ∀ v ≤ e.1, Reachable outer 0 v := by
    intro v hv
    apply intervalReachable (b := e.1) _ v (by omega) hv
    intro w _ hw
    exact oddge w (by omega) (.inl (by omega))
  have rightWalk : ∀ v, e.2 ≤ v → v < n → Reachable outer e.2 v := by
    intro v hv hnv
    apply intervalReachable (b := n - 1) _ v hv (by omega)
    intro w hw hbw
    exact oddge w (by omega) (.inr hw)
  have wrap : Reachable outer 0 (n - 1) := by
    refine .step (.inl ⟨⟨Or.inl ⟨by omega, .inr ⟨rfl, by omega, by omega⟩⟩, ?_⟩, ?_⟩)
    · exact fun h => diagonal_not_boundary hedge (h ▸ ⟨by omega, .inr ⟨rfl, by omega, by omega⟩⟩)
    · simp only [fits, second]
      omega
  refine ⟨hg, .inr he, first, second, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    dsimp [first, second]
    omega
  · intro v
    dsimp [first, second]
    omega
  · intro f hf
    have hh := hg f hf
    have hcross := noCross f hf
    simp only [fits, first, second]
    unfold crosses at hcross
    omega
  · intro v hv
    exact intervalReachable firstArc v hv.1 hv.2
  · intro v hv
    have toZero := (leftWalk e.1 (by omega)).symm
    rcases hv.2 with hl | hr
    · exact toZero.trans (leftWalk v hl)
    · exact toZero.trans (wrap.trans ((rightWalk (n - 1) (by omega) (by omega)).symm.trans
        (rightWalk v hr hv.1)))

theorem erase_insert_polygon {n : Nat} {S : Finset Edge} {e : Edge}
    (he : diagonal n e) (hn : e ∉ S) :
    eraseEdge (polygon n (insert e S)) e = polygon n S := by
  funext f
  apply propext
  simp only [eraseEdge, polygon, Finset.mem_insert]
  constructor
  · rintro ⟨hb | h | hs, hne⟩
    · exact .inl hb
    · exact False.elim (hne h)
    · exact .inr hs
  · intro hf
    refine ⟨hf.imp_right Or.inr, ?_⟩
    rintro rfl
    exact hf.elim (diagonal_not_boundary he) hn

theorem polygon_eq_boundary {α : Type*} (n : Nat) (value : Graph → α)
    (deletion : ∀ (G : Graph) (e : Edge), ParallelAlong n G e →
      value G = value (eraseEdge G e))
    (S : Finset Edge) (hd : ∀ f ∈ S, diagonal n f)
    (hn : ∀ e ∈ S, ∀ f ∈ S, ¬crosses e f) :
    value (polygon n S) = value (polygon n ∅) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert e S he ih =>
    have here : e ∈ insert e S := Finset.mem_insert_self _ _
    calc
      value (polygon n (insert e S)) = value (eraseEdge (polygon n (insert e S)) e) :=
        deletion _ _ (polygonParallel here hd (hn e here))
      _ = value (polygon n S) := congrArg value (erase_insert_polygon (hd e here) he)
      _ = value (polygon n ∅) := ih (fun f hf => hd f (Finset.mem_insert_of_mem hf))
        (fun f hf g hg => hn f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg))

def narayanaCoeff (n k : Nat) : ℚ := (n.choose k : ℚ) * (n.choose (k + 1) : ℚ) / n

theorem polygon_narayana (n : Nat) (value : Graph → Nat → ℚ)
    (deletion : ∀ (G : Graph) (e : Edge), ParallelAlong n G e →
      value G = value (eraseEdge G e))
    (cycle : value (polygon n ∅) = narayanaCoeff n)
    (S : Finset Edge) (hd : ∀ f ∈ S, diagonal n f)
    (hn : ∀ e ∈ S, ∀ f ∈ S, ¬crosses e f) :
    value (polygon n S) = narayanaCoeff n :=
  (polygon_eq_boundary n value deletion S hd hn).trans cycle

/-- The boundary already includes the hub's two endpoint spokes. -/
theorem fan_narayana (n : Nat) (value : Graph → Nat → ℚ)
    (deletion : ∀ (G : Graph) (e : Edge), ParallelAlong n G e →
      value G = value (eraseEdge G e))
    (cycle : value (polygon n ∅) = narayanaCoeff n)
    (extraSpokes : Finset Edge)
    (interior : ∀ e ∈ extraSpokes, e.1 = 0 ∧ 1 < e.2 ∧ e.2 + 1 < n) :
    value (polygon n extraSpokes) = narayanaCoeff n := by
  refine polygon_narayana n value deletion cycle _ ?_ ?_
  · intro f hf
    have h := interior f hf
    unfold diagonal
    omega
  · intro e he f hf
    have he' := (interior e he).1
    have hf' := (interior f hf).1
    unfold crosses
    omega

#print axioms polygonParallel
#print axioms ParallelAlong.commonEdge
#print axioms ParallelAlong.endpointsAfterDeletion
#print axioms polygon_eq_boundary
#print axioms polygon_narayana
#print axioms fan_narayana

end Ribbon
