import OpenMathResearch.AlternatingSignRoots

/-!
# Strict interlacing from the ordered threshold-two sign tests

The polynomials are written in the reflected variable, so positive arguments
are moduli of negative zeros. The coefficient and phase estimates supplying
the sign hypotheses are separate from this file.
-/

namespace OrderedThresholdTwoSigns

open Polynomial Set Filter

/-- Compatibility name for the shared sign-mesh root count. -/
alias roots_of_alternating_sign_mesh := OpenMathResearch.AlternatingSignRoots.roots_of_alternating_sign_mesh

/-- Compatibility name for the shared equal-degree transfer. -/
alias transfer_same_degree := OpenMathResearch.AlternatingSignRoots.transfer_same_degree

/-- Compatibility name for the shared transfer with a final root beyond the mesh. -/
alias transfer_extra_root := OpenMathResearch.AlternatingSignRoots.transfer_extra_root

private theorem signed_step_with_degree {n : ℕ} (G : ℝ[X]) (q : Fin (n / 2) → ℝ)
    (hdegree : G.natDegree = (n + 1) / 2) (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (hzero : 0 < G.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (q i))
    (hleading : 0 < (-1 : ℝ) ^ ((n + 1) / 2) * G.leadingCoeff) :
    ∃ r : Fin ((n + 1) / 2) → ℝ, StrictMono r ∧ (∀ j, 0 < r j) ∧
      (∀ i j, j.val = i.val → r j < q i) ∧
      (∀ i j, j.val = i.val + 1 → q i < r j) ∧
      G.roots = (Finset.univ.image r).val := by
  by_cases heq : (n + 1) / 2 = n / 2
  · rw [heq] at hdegree ⊢
    obtain ⟨r, hr, hbox, hgap, hroots⟩ := transfer_same_degree G q hdegree hq hpos hzero hs
    refine ⟨r, hr, fun j => (hbox j).1, ?_, ?_, hroots⟩
    · intro i j hij
      have hieq : j = i := Fin.ext hij
      simpa only [hieq] using (hbox i).2
    · intro i j hij
      apply hgap
      show i.val < j.val
      omega
  · have hnext : (n + 1) / 2 = n / 2 + 1 := by omega
    rw [hnext] at hdegree hleading ⊢
    obtain ⟨r, hr, hpositive, hgap, hroots⟩ :=
      transfer_extra_root G q hdegree hq hpos hzero hs hleading
    refine ⟨r, hr, hpositive, ?_, ?_, hroots⟩
    · intro i j hij
      have hieq : j = i.castSucc := Fin.ext hij
      simpa only [hieq] using (hgap i).1
    · intro i j hij
      have hieq : j = i.succ := Fin.ext hij
      simpa only [hieq] using (hgap i).2

/-- At degree ⌊(n+1)/2⌋, the ordered threshold-two signs at the ⌊n/2⌋
previous root moduli imply strict consecutive interlacing and exhaust all
roots of the original, unreflected next row. -/
theorem threshold_two_next_row {n : ℕ} (P : ℝ[X]) (q : Fin (n / 2) → ℝ)
    (hdegree : P.natDegree = (n + 1) / 2) (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (hzero : 0 < P.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * P.eval (-q i))
    (hleading : 0 < P.leadingCoeff) :
    ∃ r : Fin ((n + 1) / 2) → ℝ, StrictMono r ∧ (∀ j, 0 < r j) ∧
      (∀ i j, j.val = i.val → r j < q i) ∧
      (∀ i j, j.val = i.val + 1 → q i < r j) ∧
      P.roots = (Finset.univ.image (fun i => -r i)).val := by
  classical
  let G := P.comp (-X)
  have hdegreeG : G.natDegree = (n + 1) / 2 := by
    simp [G, natDegree_comp, hdegree]
  have hleadingG : 0 < (-1 : ℝ) ^ ((n + 1) / 2) * G.leadingCoeff := by
    rw [show G.leadingCoeff = (-1 : ℝ) ^ P.natDegree * P.leadingCoeff by
      exact comp_neg_X_leadingCoeff_eq P, hdegree, ← mul_assoc, ← pow_add]
    have hp : (-1 : ℝ) ^ ((n + 1) / 2 + (n + 1) / 2) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    simpa only [hp, one_mul] using hleading
  obtain ⟨r, hr, hpositive, hgap, hnext, hroots⟩ :=
    signed_step_with_degree G q hdegreeG hq hpos
      (by simpa [G, eval_comp] using hzero) (by simpa [G, eval_comp] using hs) hleadingG
  have hne : P ≠ 0 := leadingCoeff_ne_zero.mp hleading.ne'
  have hroot (i : Fin ((n + 1) / 2)) : P.IsRoot (-r i) := by
    have hmem : r i ∈ G.roots := by
      rw [hroots]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hz : G.eval (r i) = 0 := (mem_roots'.mp hmem).2
    simpa [G, eval_comp, Polynomial.IsRoot] using hz
  refine ⟨r, hr, hpositive, hgap, hnext,
    OpenMathResearch.AlternatingSignRoots.roots_of_complete_list P _ hdegree hne ?_ hroot⟩
  intro i j hij
  exact hr.injective (neg_injective hij)

end OrderedThresholdTwoSigns
