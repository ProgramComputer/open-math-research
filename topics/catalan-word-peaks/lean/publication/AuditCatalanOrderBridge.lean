import AuditCatalanWordBridge
import CatalanStrictPeaksInterlacing

namespace AuditReference

open Polynomial
open OpenMathResearch.OrientedNegativeInterlace

private def signedRoots {d : ℕ} (r : Fin d → ℝ) : List ℝ :=
  List.ofFn fun i : Fin d => -r i.rev

private theorem signedRoots_length {d : ℕ} (r : Fin d → ℝ) : (signedRoots r).length = d := by
  simp [signedRoots]

private theorem signedRoots_getD {d : ℕ} (r : Fin d → ℝ) (i : ℕ) (hi : i < d) :
    (signedRoots r).getD i 0 = -r (⟨i, hi⟩ : Fin d).rev := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [signedRoots] using hi),
    Option.getD_some]
  simp [signedRoots]

private theorem signedRoots_strict {d : ℕ} {r : Fin d → ℝ} (hr : StrictMono r) :
    (signedRoots r).Pairwise (· < ·) := by
  rw [signedRoots, List.pairwise_ofFn]
  intro i j hij
  exact neg_lt_neg (hr (Fin.rev_lt_rev.mpr hij))

private theorem signedRoots_full {p : Polynomial ℝ} {d : ℕ} {r : Fin d → ℝ}
    (hp : p ≠ 0) (hr : CompleteNegativeRoots p r) : RealRoots p (signedRoots r) := by
  classical
  have hinj : Function.Injective (fun i : Fin d => -r i.rev) :=
    neg_injective.comp (hr.2.1.injective.comp Fin.rev_injective)
  have himage : (Finset.univ.image (fun i : Fin d => -r i.rev)) =
      Finset.univ.image (fun i : Fin d => -r i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, by simp⟩
  have hroots : p.roots = (signedRoots r : Multiset ℝ) := by
    rw [hr.2.2.2, ← himage, Fin.univ_image_def]
    exact Multiset.dedup_eq_self.mpr (Multiset.coe_nodup.mpr (List.nodup_ofFn.mpr hinj))
  have hcard : p.roots.card = p.natDegree := by
    rw [hroots, Multiset.coe_card, signedRoots_length, hr.1]
  refine ⟨hp, (signedRoots_strict hr.2.1).imp (fun h => h.le), ?_⟩
  simpa [hroots] using (C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm

private theorem signedRoots_negative {d : ℕ} {r : Fin d → ℝ} (hr : ∀ i, 0 < r i) :
    ∀ x ∈ signedRoots r, x < 0 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact neg_neg_of_pos (hr i.rev)

private theorem degree_step (n : ℕ) :
    CatalanStrictPeaks.rowDegree (n+1) = CatalanStrictPeaks.rowDegree n ∨
      CatalanStrictPeaks.rowDegree (n+1) = CatalanStrictPeaks.rowDegree n + 1 := by
  unfold CatalanStrictPeaks.rowDegree
  omega

private theorem signedRoots_orientation {m d : ℕ} {r : Fin m → ℝ} {s : Fin d → ℝ}
    (hd : d = m ∨ d = m + 1) (h : Oriented r s) :
    StrictInterleaves (signedRoots r) (signedRoots s) := by
  classical
  unfold StrictInterleaves
  simp only [signedRoots_length]
  rcases hd with hdm | hdm
  · left
    refine ⟨hdm.symm, ?_, ?_⟩
    · intro i hi
      rw [signedRoots_getD r i hi, signedRoots_getD s i (by omega)]
      apply neg_lt_neg
      apply h.1
      simp [Fin.val_rev, hdm]
    · intro i hi
      rw [signedRoots_getD s i (by omega), signedRoots_getD r (i+1) hi]
      apply neg_lt_neg
      apply h.2
      simp only [Fin.val_rev, Fin.val_mk]
      omega
  · right
    refine ⟨hdm.symm, ?_⟩
    intro i hi
    constructor
    · rw [signedRoots_getD s i (by omega), signedRoots_getD r i hi]
      apply neg_lt_neg
      apply h.2
      simp only [Fin.val_rev, Fin.val_mk]
      omega
    · rw [signedRoots_getD r i hi, signedRoots_getD s (i+1) (by omega)]
      apply neg_lt_neg
      apply h.1
      simp only [Fin.val_rev, Fin.val_mk]
      omega

/-- Converts the published per-pair conclusion to increasing signed root lists for
    the independently specified word polynomial, including empty root lists. -/
theorem catalanPublished_of_successors (h : ∀ n, CatalanStrictPeaks.StrictlyInterlaces n) :
    CatalanPublished := by
  intro n
  obtain ⟨r, s, hr, hs, horder⟩ := h n
  rw [catalanPolynomial_eq, catalanPolynomial_eq]
  have hnz (k : ℕ) : CatalanStrictPeaks.C k ≠ 0 := by
    intro heq
    have hpos := CatalanStrictPeaks.eval_zero_pos k
    simp [heq] at hpos
  exact ⟨signedRoots r, signedRoots s, signedRoots_full (hnz n) hr,
    signedRoots_full (hnz (n+1)) hs, signedRoots_strict hr.2.1, signedRoots_strict hs.2.1,
    signedRoots_negative hr.2.2.1, signedRoots_negative hs.2.2.1,
    signedRoots_orientation (degree_step n) horder⟩

theorem catalanOriginal_of_published (h : CatalanPublished) : CatalanOriginal := by
  intro n
  obtain ⟨xs, ys, hx, hy, _, _, _, _, hh⟩ := h n
  refine ⟨xs, ys, hx, hy, ?_⟩
  rcases hh with ⟨hl, h₁, h₂⟩ | ⟨hl, hchain⟩
  · exact Or.inl ⟨hl, fun i hi => (h₁ i hi).le, fun i hi => (h₂ i hi).le⟩
  · exact Or.inr ⟨hl, fun i hi => ⟨(hchain i hi).1.le, (hchain i hi).2.le⟩⟩

#print axioms catalanPublished_of_successors
#print axioms catalanOriginal_of_published

end AuditReference
