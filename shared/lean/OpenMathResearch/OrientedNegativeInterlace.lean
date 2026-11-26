import OpenMathResearch.AlternatingSignRoots

/-!
# Oriented negative interlacing from signed values at test points

In the reflected variable, every new root modulus precedes the corresponding
old modulus. The old moduli separate the new ones, and a degree increase
gives one final new modulus beyond all the old ones.
-/

namespace OpenMathResearch.OrientedNegativeInterlace

open Polynomial

/-- Strictly increasing positive moduli of all simple negative roots. -/
def CompleteNegativeRoots {d : ℕ} (P : ℝ[X]) (r : Fin d → ℝ) : Prop :=
  P.natDegree = d ∧ StrictMono r ∧ (∀ i, 0 < r i) ∧
    P.roots = (Finset.univ.image (fun i => -r i)).val

/-- The inequalities encoding the orientation in increasing modulus order. -/
def Oriented {m d : ℕ} (old : Fin m → ℝ) (new : Fin d → ℝ) : Prop :=
  (∀ i j, j.val = i.val → new j < old i) ∧
  (∀ i j, j.val = i.val + 1 → old i < new j)

/-- Positive constant and leading coefficients and alternating signs at
negative test points isolate all the next roots, for either degree change.
The shared sign transfers already treat both degree patterns. -/
theorem roots_of_signed_test_points {m d : ℕ} (P : ℝ[X]) (old : Fin m → ℝ)
    (hdegree : P.natDegree = d) (hd : d = m ∨ d = m + 1)
    (hold : StrictMono old) (hpos : ∀ i, 0 < old i)
    (hzero : 0 < P.eval 0) (hlead : 0 < P.leadingCoeff)
    (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * P.eval (-old i)) :
    ∃ new : Fin d → ℝ, CompleteNegativeRoots P new ∧ Oriented old new := by
  let G := P.comp (-X)
  have hdegreeG : G.natDegree = d := by simp [G, natDegree_comp, hdegree]
  have hzeroG : 0 < G.eval 0 := by simpa [G, eval_comp] using hzero
  have hsG (i : Fin m) : 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (old i) := by
    simpa [G, eval_comp] using hs i
  have hleadG : 0 < (-1 : ℝ) ^ d * G.leadingCoeff := by
    rw [show G.leadingCoeff = (-1 : ℝ) ^ P.natDegree * P.leadingCoeff from
      comp_neg_X_leadingCoeff_eq P, hdegree, ← mul_assoc, ← pow_add]
    have hparity : (-1 : ℝ) ^ (d + d) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    simpa only [hparity, one_mul] using hlead
  have hnew : ∃ new : Fin d → ℝ, StrictMono new ∧ (∀ i, 0 < new i) ∧
      G.roots = (Finset.univ.image new).val ∧ Oriented old new := by
    rcases hd with hsame | hextra
    · rw [hsame] at hdegreeG ⊢
      obtain ⟨new, hmono, hbox, hgap, hroots⟩ :=
        AlternatingSignRoots.transfer_same_degree G old hdegreeG hold hpos hzeroG hsG
      refine ⟨new, hmono, fun i => (hbox i).1, hroots, ?_, ?_⟩
      · intro i j hj
        have heq : j = i := Fin.ext hj
        simpa only [heq] using (hbox i).2
      · intro i j hj
        exact hgap i j (by change i.val < j.val; omega)
    · rw [hextra] at hdegreeG hleadG ⊢
      obtain ⟨new, hmono, hpositive, hgap, hroots⟩ :=
        AlternatingSignRoots.transfer_extra_root G old hdegreeG hold hpos hzeroG hsG hleadG
      refine ⟨new, hmono, hpositive, hroots, ?_, ?_⟩
      · intro i j hj
        have heq : j = i.castSucc := Fin.ext hj
        simpa only [heq] using (hgap i).1
      · intro i j hj
        have heq : j = i.succ := Fin.ext hj
        simpa only [heq] using (hgap i).2
  obtain ⟨new, hmono, hpositive, hroots, hOriented⟩ := hnew
  have hne : P ≠ 0 := leadingCoeff_ne_zero.mp hlead.ne'
  have hr (i : Fin d) : P.IsRoot (-new i) := by
    have hmem : new i ∈ G.roots := by
      rw [hroots]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa [G, eval_comp, Polynomial.IsRoot] using (mem_roots'.mp hmem).2
  refine ⟨new, ⟨hdegree, hmono, hpositive, ?_⟩, hOriented⟩
  exact AlternatingSignRoots.roots_of_complete_list P (fun i => -new i) hdegree hne
    (neg_injective.comp hmono.injective) hr

/-- If the test points are the full old root list, the same transfer proves
strict consecutive interlacing of the original negative root lists. -/
theorem next_of_signs_at_all_old_roots {m d : ℕ} {oldRow nextRow : ℝ[X]}
    {old : Fin m → ℝ} (hOld : CompleteNegativeRoots oldRow old)
    (hdegree : nextRow.natDegree = d) (hd : d = m ∨ d = m + 1)
    (hzero : 0 < nextRow.eval 0) (hlead : 0 < nextRow.leadingCoeff)
    (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * nextRow.eval (-old i)) :
    ∃ new : Fin d → ℝ, CompleteNegativeRoots nextRow new ∧ Oriented old new :=
  roots_of_signed_test_points nextRow old hdegree hd hOld.2.1 hOld.2.2.1 hzero hlead hs

end OpenMathResearch.OrientedNegativeInterlace
