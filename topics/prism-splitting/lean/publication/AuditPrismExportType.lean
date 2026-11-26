import PrismFamilyInterlacing

/-! The published endpoint and infinite-family theorems have no extra hypotheses.
Normalization and the family root predicate are spelled out here. -/

namespace AuditExportType

open PrismSplit PrismFamily

noncomputable def sliceNumerator {n : ℕ} (caps : Fin n → ℕ) (level : ℕ)
    (hn : (realFinSlice caps level).Nonempty) :
    PowerSeries Int :=
  (1 - PowerSeries.X) ^
      (Module.finrank ℝ (affineSpan ℝ (realFinSlice caps level)).direction + 1) *
    PowerSeries.mk fun q => (finLatticeCount caps level q hn : Int)

/-- Full disproof at level six, stated using the real zero sets. -/
theorem prismSix :
    ∃ p q : Polynomial Int,
      p.natDegree = 9 ∧ q.natDegree = 10 ∧
      (p : PowerSeries Int) = sliceNumerator unsplitFinCaps 6 unsplitFinNonempty ∧
      (q : PowerSeries Int) = sliceNumerator splitFinCaps 6 splitFinNonempty ∧
      ¬ ∃ xs ys : List ℝ,
        (∀ x : ℝ, x ∈ xs ↔ p.eval₂ (Int.castRingHom ℝ) x = 0) ∧
        (∀ y : ℝ, y ∈ ys ↔ q.eval₂ (Int.castRingHom ℝ) y = 0) ∧
        alternatingRoots xs ys :=
  PrismSplit.finBoxSplitCounterexample

/-- Full family for levels b+1 ≥ 7, stated with multiplicities. -/
theorem prismFamily :
    ∀ b : ℕ, 6 ≤ b → ∃ p q : Polynomial Int,
      p.natDegree = 2 * b - 1 ∧ q.natDegree = 2 * b ∧
      (p : PowerSeries Int) = sliceNumerator (beforeFinCaps b) (b + 1) (beforeFinNonempty b) ∧
      (q : PowerSeries Int) = sliceNumerator (afterFinCaps b) (b + 1) (afterFinNonempty b) ∧
      ¬ (let P := p.map (Int.castRingHom ℝ)
         let Q := q.map (Int.castRingHom ℝ)
         P.roots.card = P.natDegree ∧ Q.roots.card = Q.natDegree ∧ ∃ xs ys : List ℝ,
           (xs : Multiset ℝ) = P.roots ∧ (ys : Multiset ℝ) = Q.roots ∧ alternatingRoots xs ys) :=
  by simpa only [WeakRealInterlaces, Polynomial.splits_iff_card_roots] using
    PrismFamily.familyBoxSplitCounterexample

#print axioms prismSix
#print axioms prismFamily

end AuditExportType
