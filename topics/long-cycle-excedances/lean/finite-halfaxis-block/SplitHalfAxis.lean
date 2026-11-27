import HalfAxisDyadic

namespace RepositoryQuotientAudit

open LongCycleFinite

private def signedEndpoint (x : LongCycleFinite.Dyadic) : LongCycleFinite.Dyadic :=
  ⟨-x.numer, x.shift⟩

private def isOdd (i : ℕ) : Bool := decide (i % 2 = 1)

def halfAxisPointOK (p q : List ℤ) (i : ℕ) (w : HalfAxisDyadicWindow) : Bool :=
  LongCycleFinite.Dyadic.zero.less w.lower && w.lower.less w.upper &&
    w.upper.less ⟨1, 0⟩ &&
    roundedSign (isOdd i) p (signedEndpoint w.lower) &&
    roundedSign (!isOdd i) p (signedEndpoint w.upper) &&
    roundedSign (isOdd (i + 1)) q (signedEndpoint w.lower) &&
    roundedSign (isOdd (i + 1)) q (signedEndpoint w.upper)

def halfAxisCenterOK (n : ℕ) (q : List ℤ) : Bool :=
  if (n - 2) % 2 = 1 then roundedSign (isOdd ((n - 2) / 2 + 1)) q ⟨-1, 0⟩ else true

/-- Separate each point's directed Horner checks from adjacent ordering. The
old quadratic all-pairs ordering test follows from the adjacent comparisons. -/
theorem halfAxisDyadicOK_of_split {n : ℕ} (p q : List ℤ)
    (ws : Fin ((n - 2) / 2) → HalfAxisDyadicWindow)
    (hpoint : ∀ i, halfAxisPointOK p q i.val (ws i) = true)
    (hjoin : ∀ (i : Fin ((n - 2) / 2 - 1)),
      (ws ⟨i.val, by omega⟩).upper.less (ws ⟨i.val + 1, by omega⟩).lower = true)
    (hcenter : halfAxisCenterOK n q = true) :
    halfAxisDyadicOK n p q ws = true := by
  let d := (n - 2) / 2
  have hwithin (i : Fin d) : (ws i).lower.value < (ws i).upper.value := by
    have hi := hpoint i
    simp only [halfAxisPointOK, Bool.and_eq_true_iff] at hi
    exact (LongCycleFinite.Dyadic.less_iff _ _).mp hi.1.1.1.1.1.2
  have hchain (i j : Fin d) (hij : i.val + 1 = j.val) :
      (ws i).upper.value < (ws j).lower.value := by
    let t : Fin (d - 1) := ⟨i.val, by have hj := j.isLt; omega⟩
    have hb := (LongCycleFinite.Dyadic.less_iff _ _).mp (hjoin t)
    have he : (⟨t.val + 1, by have ht := t.isLt; omega⟩ : Fin d) = j := Fin.ext hij
    simpa only [he] using hb
  have aux (D : ℕ) (f : Fin D → ℝ)
      (step : ∀ i j : Fin D, i.val + 1 = j.val → f i < f j) : StrictMono f := by
    cases D with
    | zero => intro i; exact Fin.elim0 i
    | succ D =>
      exact Fin.strictMono_iff_lt_succ.mpr (fun i => step i.castSucc i.succ rfl)
  have hmono : StrictMono (fun i : Fin d => (ws i).lower.value) :=
    aux d _ (fun i j hj => (hwithin i).trans (hchain i j hj))
  unfold halfAxisDyadicOK
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hcenter⟩
  apply List.all_eq_true.mpr
  intro i _
  change (halfAxisPointOK p q i.val (ws i) &&
      (List.finRange d).all (fun j => if i < j then (ws i).upper.less (ws j).lower else true)) = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hpoint i, ?_⟩
  apply List.all_eq_true.mpr
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij]
    apply (LongCycleFinite.Dyadic.less_iff _ _).mpr
    have hv : i.val < j.val := hij
    let t : Fin d := ⟨i.val + 1, by have hj := j.isLt; omega⟩
    have ht : t ≤ j := by change i.val + 1 ≤ j.val; omega
    exact (hchain i t rfl).trans_le (hmono.monotone ht)
  · simp [hij]

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.halfAxisDyadicOK_of_split
