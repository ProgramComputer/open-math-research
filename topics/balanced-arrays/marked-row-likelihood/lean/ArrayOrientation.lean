import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

namespace BalancedRowTilt

/-- An uncolored refinement in each labeled column. Two-cycles are paired exclusive
cells. At a fixed point both arrays take the supplied common bit. Extra labeled
rows, including auxiliary slots, can be included in the row index. -/
@[ext] structure ColumnPairing (n d : ℕ) where
  mate : Fin d → Fin n → Fin n
  twice : ∀ j i, mate j (mate j i) = i
  common : Fin n → Fin d → Bool

namespace ColumnPairing

variable {n d : ℕ} (P : ColumnPairing n d)

abbrev ArrayPair := (Fin n → Fin d → Bool) × (Fin n → Fin d → Bool)

/-- Every paired edge is named by its smaller endpoint and its labeled column. -/
abbrev Edge := {p : Fin n × Fin d // p.1 < P.mate p.2 p.1}

abbrev Orientation := P.Edge → Bool

def red (o : P.Orientation) (i : Fin n) (j : Fin d) : Bool :=
  if h : i < P.mate j i then o ⟨(i, j), h⟩
  else if h' : P.mate j i < i then
    !(o ⟨(P.mate j i, j), by simpa only [P.twice] using h'⟩)
  else P.common i j

def decode (o : P.Orientation) : ArrayPair (n := n) (d := d) :=
  (P.red o, fun i j => P.red o (P.mate j i) j)

/-- This predicate specifies the fiber directly on two binary matrices. -/
def Compatible (X : ArrayPair (n := n) (d := d)) : Prop :=
  ∀ i j, X.2 i j = X.1 (P.mate j i) j ∧
    (if P.mate j i = i then X.1 i j = P.common i j
     else X.1 (P.mate j i) j = !(X.1 i j))

theorem red_at_low (o : P.Orientation) {i j} (h : i < P.mate j i) :
    P.red o i j = o ⟨(i, j), h⟩ := by simp [red, h]

theorem red_at_fixed (o : P.Orientation) {i j} (h : P.mate j i = i) :
    P.red o i j = P.common i j := by simp [red, h]

theorem red_at_mate (o : P.Orientation) {i j} (h : P.mate j i ≠ i) :
    P.red o (P.mate j i) j = !(P.red o i j) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [red, P.twice, h', not_lt_of_gt h']
  · simp [red, P.twice, h', not_lt_of_gt h']

theorem decode_compatible (o : P.Orientation) : P.Compatible (P.decode o) := by
  intro i j
  refine ⟨rfl, ?_⟩
  by_cases h : P.mate j i = i
  · simpa only [if_pos h] using P.red_at_fixed o h
  · simpa only [if_neg h] using P.red_at_mate o h

def encode (X : ArrayPair (n := n) (d := d)) : P.Orientation :=
  fun e => X.1 e.val.1 e.val.2

theorem encode_decode (o : P.Orientation) : P.encode (P.decode o) = o := by
  funext e
  exact P.red_at_low o e.property

theorem decode_encode (X : ArrayPair (n := n) (d := d)) (hX : P.Compatible X) :
    P.decode (P.encode X) = X := by
  have hred (i : Fin n) (j : Fin d) : P.red (P.encode X) i j = X.1 i j := by
    rcases lt_trichotomy i (P.mate j i) with h | h | h
    · exact P.red_at_low _ h
    · have hf : X.1 i j = P.common i j := by
        simpa only [if_pos h.symm] using (hX i j).2
      exact (P.red_at_fixed _ h.symm).trans hf.symm
    · have hn := ne_of_lt h
      have hc : X.1 (P.mate j i) j = !(X.1 i j) := by
        simpa only [if_neg hn] using (hX i j).2
      simp [red, not_lt_of_gt h, h, encode, hc]
  apply Prod.ext
  · funext i j
    exact hred i j
  · funext i j
    exact (hred (P.mate j i) j).trans (hX i j).1.symm

/-- Orientations of the uncolored pairing are equivalent to the fiber of actual
labeled array pairs, with no row or column quotient. -/
def arrayEquiv : P.Orientation ≃ {X // P.Compatible X} where
  toFun o := ⟨P.decode o, P.decode_compatible o⟩
  invFun X := P.encode X.val
  left_inv := P.encode_decode
  right_inv X := Subtype.ext (P.decode_encode X.val X.property)

/-- Row constraints and prescribed colors of auxiliary slots can be imposed on
both sides of the bijection simultaneously. -/
def constrainedEquiv (ok : ArrayPair (n := n) (d := d) → Prop) :
    {o : P.Orientation // ok (P.decode o)} ≃ {X // P.Compatible X ∧ ok X} where
  toFun o := ⟨P.decode o.val, P.decode_compatible o.val, o.property⟩
  invFun X := ⟨P.encode X.val, (P.decode_encode X.val X.property.1).symm ▸ X.property.2⟩
  left_inv o := Subtype.ext (P.encode_decode o.val)
  right_inv X := Subtype.ext (P.decode_encode X.val X.property.1)

theorem constrained_count (ok : ArrayPair (n := n) (d := d) → Prop) :
    Nat.card {o : P.Orientation // ok (P.decode o)} =
      Nat.card {X // P.Compatible X ∧ ok X} :=
  Nat.card_congr (P.constrainedEquiv ok)

/-- The directed edge goes from its red endpoint to its blue endpoint. -/
def tail (o : P.Orientation) (e : P.Edge) : Fin n :=
  if o e then e.val.1 else P.mate e.val.2 e.val.1

def edgeAt (i : Fin n) (j : Fin d) (h : P.mate j i ≠ i) : P.Edge :=
  if hl : i < P.mate j i then ⟨(i, j), hl⟩
  else ⟨(P.mate j i, j), by
    simpa only [P.twice] using lt_of_le_of_ne (le_of_not_gt hl) h⟩

@[simp] theorem edgeAt_col {i j} (h : P.mate j i ≠ i) :
    (P.edgeAt i j h).val.2 = j := by
  unfold edgeAt
  split <;> rfl

theorem edgeAt_tail (o : P.Orientation) (e : P.Edge) :
    ∃ h : P.mate e.val.2 (P.tail o e) ≠ P.tail o e,
      P.edgeAt (P.tail o e) e.val.2 h = e ∧ P.red o (P.tail o e) e.val.2 = true := by
  obtain ⟨⟨i, j⟩, hl⟩ := e
  change i < P.mate j i at hl
  let e : P.Edge := ⟨(i, j), hl⟩
  change ∃ h : P.mate j (P.tail o e) ≠ P.tail o e,
    P.edgeAt (P.tail o e) j h = e ∧ P.red o (P.tail o e) j = true
  cases ho : o e with
  | true =>
    simp only [tail, ho, Bool.true_eq, if_true]
    exact ⟨ne_of_gt hl, by simp [edgeAt, hl, e], (P.red_at_low o hl).trans ho⟩
  | false =>
    simp only [tail, ho, Bool.false_eq_true, if_false]
    have hn : P.mate j (P.mate j i) ≠ P.mate j i := by simpa only [P.twice] using ne_of_lt hl
    refine ⟨hn, ?_, ?_⟩
    · apply Subtype.ext
      simp [edgeAt, e, P.twice, not_lt_of_gt hl]
    · rw [P.red_at_mate o (ne_of_gt hl), P.red_at_low o hl]
      change (!o e) = true
      simp [ho]

theorem tail_edgeAt {i j} (o : P.Orientation) (h : P.mate j i ≠ i)
    (hred : P.red o i j = true) : P.tail o (P.edgeAt i j h) = i := by
  rcases lt_or_gt_of_ne h with hl | hl
  · have hr : P.red o (P.mate j i) j = false := by simp [P.red_at_mate o h, hred]
    have hlow : P.mate j i < P.mate j (P.mate j i) := by simpa only [P.twice] using hl
    rw [P.red_at_low o hlow] at hr
    simp [tail, edgeAt, not_lt_of_gt hl, hr, P.twice]
  · rw [P.red_at_low o hl] at hred
    simp [tail, edgeAt, hl, hred]

/-- The outgoing edges at a row correspond to its exclusive red cells. -/
def outgoingEquiv (o : P.Orientation) (i : Fin n) :
    {j // P.mate j i ≠ i ∧ P.red o i j = true} ≃ {e // P.tail o e = i} where
  toFun j := ⟨P.edgeAt i j.val j.property.1, P.tail_edgeAt o j.property.1 j.property.2⟩
  invFun e := ⟨e.val.val.2, by
    obtain ⟨hn, _, hr⟩ := P.edgeAt_tail o e.val
    simpa only [e.property] using And.intro hn hr⟩
  left_inv j := Subtype.ext (P.edgeAt_col j.property.1)
  right_inv e := by
    apply Subtype.ext
    obtain ⟨hn, he, _⟩ := P.edgeAt_tail o e.val
    obtain ⟨e, rfl⟩ := e
    exact he

private def splitOnes {α : Type*} (bit common : α → Bool) (fixed : α → Prop)
    [DecidablePred fixed] (agree : ∀ x, fixed x → bit x = common x) :
    {x // bit x = true} ≃
      {x // fixed x ∧ common x = true} ⊕ {x // ¬ fixed x ∧ bit x = true} where
  toFun x := if h : fixed x then Sum.inl ⟨x.val, h, (agree x.val h).symm.trans x.property⟩
    else Sum.inr ⟨x.val, h, x.property⟩
  invFun
    | Sum.inl x => ⟨x.val, (agree x.val x.property.1).trans x.property.2⟩
    | Sum.inr x => ⟨x.val, x.property.2⟩
  left_inv x := by by_cases h : fixed x.val <;> simp [h]
  right_inv
    | Sum.inl x => by simp [x.property.1]
    | Sum.inr x => by simp [x.property.1]

def reversed (o : P.Orientation) : P.Orientation := fun e => !(o e)

theorem red_reversed (o : P.Orientation) (i : Fin n) (j : Fin d) :
    P.red (P.reversed o) i j = P.red o (P.mate j i) j := by
  rcases lt_trichotomy i (P.mate j i) with h | h | h
  · simp [red, reversed, P.twice, h, not_lt_of_gt h]
  · simp [red, h.symm]
  · simp [red, reversed, P.twice, h, not_lt_of_gt h]

noncomputable def rowSize (X : Fin n → Fin d → Bool) (i : Fin n) :=
  Nat.card {j // X i j = true}

noncomputable def columnSize (X : Fin n → Fin d → Bool) (j : Fin d) :=
  Nat.card {i // X i j = true}

noncomputable def commonRow (i : Fin n) :=
  Nat.card {j // P.mate j i = i ∧ P.common i j = true}

noncomputable def outdegree (o : P.Orientation) (i : Fin n) := Nat.card {e // P.tail o e = i}

theorem red_row_size (o : P.Orientation) (i : Fin n) :
    rowSize (P.decode o).1 i = P.commonRow i + P.outdegree o i := by
  let parts := splitOnes (P.red o i) (P.common i) (fun j => P.mate j i = i)
    (fun _ h => P.red_at_fixed o h)
  let eqv := parts.trans (Equiv.sumCongr (Equiv.refl _) (P.outgoingEquiv o i))
  exact (Nat.card_congr eqv).trans Nat.card_sum

theorem blue_row_size (o : P.Orientation) (i : Fin n) :
    rowSize (P.decode o).2 i = P.commonRow i + P.outdegree (P.reversed o) i := by
  have eq : (P.decode o).2 = P.red (P.reversed o) := by
    funext a j
    exact (P.red_reversed o a j).symm
  rw [eq]
  exact P.red_row_size (P.reversed o) i

/-- One outgoing endpoint occurs per paired edge, also when restricting to a
particular column. Its inverse sends a red cell to its uniquely determined edge. -/
def columnEdgeEquiv (o : P.Orientation) (j : Fin d) :
    {i // P.mate j i ≠ i ∧ P.red o i j = true} ≃ {e : P.Edge // e.val.2 = j} where
  toFun i := ⟨P.edgeAt i.val j i.property.1, P.edgeAt_col i.property.1⟩
  invFun e := ⟨P.tail o e.val, by
    obtain ⟨hn, _, hr⟩ := P.edgeAt_tail o e.val
    simpa only [e.property] using And.intro hn hr⟩
  left_inv i := Subtype.ext (P.tail_edgeAt o i.property.1 i.property.2)
  right_inv e := by
    apply Subtype.ext
    obtain ⟨hn, he, _⟩ := P.edgeAt_tail o e.val
    obtain ⟨e, rfl⟩ := e
    exact he

noncomputable def columnQuota (j : Fin d) :=
  Nat.card {i // P.mate j i = i ∧ P.common i j = true} + Nat.card {e : P.Edge // e.val.2 = j}

theorem red_column_size (o : P.Orientation) (j : Fin d) :
    columnSize (P.decode o).1 j = P.columnQuota j := by
  let parts := splitOnes (fun i => P.red o i j) (fun i => P.common i j)
    (fun i => P.mate j i = i) (fun _ h => P.red_at_fixed o h)
  let eqv := parts.trans (Equiv.sumCongr (Equiv.refl _) (P.columnEdgeEquiv o j))
  exact (Nat.card_congr eqv).trans Nat.card_sum

theorem blue_column_size (o : P.Orientation) (j : Fin d) :
    columnSize (P.decode o).2 j = P.columnQuota j := by
  have eq : (P.decode o).2 = P.red (P.reversed o) := by
    funext i c
    exact (P.red_reversed o i c).symm
  rw [eq]
  exact P.red_column_size (P.reversed o) j

/-- Compare the cardinalities with *different* red and blue row conditions
(including marked sizes and forced auxiliary colors represented by row sizes).
Column sums of both augmented arrays are already fixed by the pairing. -/
theorem row_constrained_count (redOK blueOK : Fin n → ℕ → Prop) :
    Nat.card {X : ArrayPair (n := n) (d := d) // P.Compatible X ∧
      ∀ i, redOK i (rowSize X.1 i) ∧ blueOK i (rowSize X.2 i)} =
    Nat.card {o : P.Orientation // ∀ i, redOK i (P.commonRow i + P.outdegree o i) ∧
      blueOK i (P.commonRow i + P.outdegree (P.reversed o) i)} := by
  rw [← P.constrained_count (fun X => ∀ i, redOK i (rowSize X.1 i) ∧ blueOK i (rowSize X.2 i))]
  simp only [P.red_row_size, P.blue_row_size]

/-- A vertex label may split a row into several vertices. This keeps the
incidence at a marked cell, including a singleton, visible to the graph. -/
def splitOutgoingEquiv {V : Type*} (vertex : Fin n → Fin d → V) (v : V)
    (o : P.Orientation) :
    {p : Fin n × Fin d // P.mate p.2 p.1 ≠ p.1 ∧ P.red o p.1 p.2 = true ∧
      vertex p.1 p.2 = v} ≃ {e : P.Edge // vertex (P.tail o e) e.val.2 = v} where
  toFun p := ⟨P.edgeAt p.val.1 p.val.2 p.property.1, by
    rw [P.tail_edgeAt o p.property.1 p.property.2.1, P.edgeAt_col]
    exact p.property.2.2⟩
  invFun e := ⟨(P.tail o e.val, e.val.val.2), by
    obtain ⟨hn, _, hr⟩ := P.edgeAt_tail o e.val
    exact ⟨hn, hr, e.property⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (P.tail_edgeAt o p.property.1 p.property.2.1) (P.edgeAt_col p.property.1)
  right_inv e := by
    obtain ⟨_, he, _⟩ := P.edgeAt_tail o e.val
    exact Subtype.ext he

abbrev RedOnly (X : ArrayPair (n := n) (d := d)) (j : Fin d) (i : Fin n) :=
  X.1 i j = true ∧ X.2 i j = false

abbrev BlueOnly (X : ArrayPair (n := n) (d := d)) (j : Fin d) (i : Fin n) :=
  X.1 i j = false ∧ X.2 i j = true

abbrev Matchings (X : ArrayPair (n := n) (d := d)) :=
  ∀ j, {i // RedOnly X j i} ≃ {i // BlueOnly X j i}

private def partner {X : ArrayPair (n := n) (d := d)} (M : Matchings X)
    (j : Fin d) (i : Fin n) : Fin n :=
  if hr : RedOnly X j i then (M j ⟨i, hr⟩).val
  else if hb : BlueOnly X j i then ((M j).symm ⟨i, hb⟩).val
  else i

private theorem partner_red {X : ArrayPair (n := n) (d := d)} (M : Matchings X)
    {j i} (h : RedOnly X j i) : partner M j i = (M j ⟨i, h⟩).val := by
  simp only [partner, dif_pos h]

private theorem partner_blue {X : ArrayPair (n := n) (d := d)} (M : Matchings X)
    {j i} (h : BlueOnly X j i) : partner M j i = ((M j).symm ⟨i, h⟩).val := by
  have nr : ¬ RedOnly X j i := by simp [RedOnly, h.1]
  simp only [partner, dif_neg nr, dif_pos h]

/-- Forget colors of the independently chosen labeled matchings in the columns. -/
def ofMatchings (X : ArrayPair (n := n) (d := d)) (M : Matchings X) : ColumnPairing n d where
  mate := partner M
  twice j i := by
    by_cases hr : RedOnly X j i
    · rw [partner_red M hr, partner_blue M (M j ⟨i,hr⟩).property]
      simp
    by_cases hb : BlueOnly X j i
    · rw [partner_blue M hb, partner_red M ((M j).symm ⟨i,hb⟩).property]
      simp
    · simp [partner, hr, hb]
  common i j := X.1 i j && X.2 i j

theorem ofMatchings_compatible (X : ArrayPair (n := n) (d := d)) (M : Matchings X) :
    (ofMatchings X M).Compatible X := by
  intro i j
  change X.2 i j = X.1 (partner M j i) j ∧
    (if partner M j i = i then X.1 i j = (X.1 i j && X.2 i j)
     else X.1 (partner M j i) j = !(X.1 i j))
  cases hr : X.1 i j <;> cases hb : X.2 i j
  · simp [partner, RedOnly, BlueOnly, hr, hb]
  · have h := partner_blue M (And.intro hr hb)
    have hc := ((M j).symm ⟨i, And.intro hr hb⟩).property.1
    have ne : ((M j).symm ⟨i, And.intro hr hb⟩).val ≠ i := by
      intro eq
      rw [eq, hr] at hc
      contradiction
    simp [h, ne, hc]
  · have h := partner_red M (And.intro hr hb)
    have hc := (M j ⟨i, And.intro hr hb⟩).property.1
    have ne : (M j ⟨i, And.intro hr hb⟩).val ≠ i := by
      intro eq
      rw [eq, hr] at hc
      contradiction
    simp [h, ne, hc]
  · simp [partner, RedOnly, BlueOnly, hr, hb]

/-- With the two original arrays fixed, every uncolored refinement restricts
to a bijection of the two exclusive sets in each column. -/
def toMatchings {X : ArrayPair (n := n) (d := d)} (h : P.Compatible X) : Matchings X :=
  fun j => {
    toFun := fun i => ⟨P.mate j i.val, by
      refine ⟨(h i.val j).1.symm.trans i.property.2, ?_⟩
      simpa only [P.twice] using (h (P.mate j i.val) j).1.trans (by simpa only [P.twice] using i.property.1)⟩
    invFun := fun i => ⟨P.mate j i.val, by
      refine ⟨(h i.val j).1.symm.trans i.property.2, ?_⟩
      simpa only [P.twice] using (h (P.mate j i.val) j).1.trans (by simpa only [P.twice] using i.property.1)⟩
    left_inv := fun i => Subtype.ext (P.twice j i.val)
    right_inv := fun i => Subtype.ext (P.twice j i.val)
  }

private theorem fixed_of_neither {X : ArrayPair (n := n) (d := d)} (h : P.Compatible X)
    {i j} (hr : ¬ RedOnly X j i) (hb : ¬ BlueOnly X j i) : P.mate j i = i := by
  by_contra hn
  have hc : X.2 i j = !(X.1 i j) := (h i j).1.trans (by simpa only [if_neg hn] using (h i j).2)
  cases hbit : X.1 i j <;> simp_all [RedOnly, BlueOnly]

def IsRefinement (X : ArrayPair (n := n) (d := d)) : Prop :=
  P.Compatible X ∧ P.common = fun i j => X.1 i j && X.2 i j

/-- Normalizing the ignored common bit at an exclusive slot avoids counting
multiple copies of the same uncolored pairing. -/
def refinementsEquiv (X : ArrayPair (n := n) (d := d)) :
    Matchings X ≃ {P : ColumnPairing n d // P.IsRefinement X} where
  toFun M := ⟨ofMatchings X M, ofMatchings_compatible X M, rfl⟩
  invFun Q := Q.val.toMatchings Q.property.1
  left_inv M := by
    funext j
    apply Equiv.ext
    intro i
    exact Subtype.ext (partner_red M i.property)
  right_inv Q := by
    apply Subtype.ext
    apply ColumnPairing.ext
    · funext j i
      change partner (Q.val.toMatchings Q.property.1) j i = Q.val.mate j i
      by_cases hr : RedOnly X j i
      · exact partner_red _ hr
      by_cases hb : BlueOnly X j i
      · exact partner_blue _ hb
      · simpa only [partner, dif_neg hr, dif_neg hb] using
          (Q.val.fixed_of_neither Q.property.1 hr hb).symm
    · exact Q.property.2.symm

theorem refinement_count (X : ArrayPair (n := n) (d := d)) :
    Nat.card {P : ColumnPairing n d // P.IsRefinement X} = Nat.card (Matchings X) :=
  Nat.card_congr (refinementsEquiv X).symm

theorem refinement_count_factorial (X : ArrayPair (n := n) (d := d)) (M : Matchings X) :
    Nat.card {P : ColumnPairing n d // P.IsRefinement X} =
      ∏ j, (Fintype.card {i // RedOnly X j i}).factorial := by
  classical
  rw [refinement_count, Nat.card_eq_fintype_card]
  unfold Matchings
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun j _ => Fintype.card_equiv (M j)

/-- Equal augmented column totals suffice for the factorial formula, including
zero exclusive slots. The exclusive sets need no prescribed identifications. -/
theorem refinement_count_of_quotas (X : ArrayPair (n := n) (d := d))
    (hq : ∀ j, columnSize X.1 j = columnSize X.2 j) :
    Nat.card {P : ColumnPairing n d // P.IsRefinement X} =
      ∏ j, (Fintype.card {i // RedOnly X j i}).factorial := by
  classical
  apply refinement_count_factorial
  intro j
  apply Fintype.equivOfCardEq
  have partition (bit other : Fin n → Bool) :
      Nat.card {i // bit i = true} =
        Nat.card {i // other i = true ∧ bit i = true} +
        Nat.card {i // other i = false ∧ bit i = true} := by
    let eqv := splitOnes bit bit (fun i => other i = true) (fun _ _ => rfl)
    rw [Nat.card_congr eqv, Nat.card_sum]
    simp
  have h := hq j
  unfold columnSize at h
  rw [partition (fun i => X.1 i j) (fun i => X.2 i j),
    partition (fun i => X.2 i j) (fun i => X.1 i j)] at h
  have ce : Nat.card {i // X.2 i j = true ∧ X.1 i j = true} =
      Nat.card {i // X.1 i j = true ∧ X.2 i j = true} := by simp_rw [@and_comm (X.2 _ j = true)]
  rw [ce] at h
  have hb := Nat.add_left_cancel h
  simp only [RedOnly, BlueOnly, ← Nat.card_eq_fintype_card]
  simpa only [@and_comm (X.2 _ j = false)] using hb

end ColumnPairing
end BalancedRowTilt

#print axioms BalancedRowTilt.ColumnPairing.arrayEquiv
#print axioms BalancedRowTilt.ColumnPairing.constrained_count
#print axioms BalancedRowTilt.ColumnPairing.outgoingEquiv
#print axioms BalancedRowTilt.ColumnPairing.red_row_size
#print axioms BalancedRowTilt.ColumnPairing.blue_row_size
#print axioms BalancedRowTilt.ColumnPairing.red_column_size
#print axioms BalancedRowTilt.ColumnPairing.blue_column_size
#print axioms BalancedRowTilt.ColumnPairing.row_constrained_count
#print axioms BalancedRowTilt.ColumnPairing.splitOutgoingEquiv
#print axioms BalancedRowTilt.ColumnPairing.ofMatchings_compatible
#print axioms BalancedRowTilt.ColumnPairing.refinementsEquiv
#print axioms BalancedRowTilt.ColumnPairing.refinement_count_of_quotas
