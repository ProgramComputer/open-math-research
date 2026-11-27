import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Concatenate exterior and middle singleton witnesses in increasing modulus.
The exponent is the sign for the original successor row before division by X. -/
theorem join_signed_root_moduli {n H : ℕ} {P Q : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hc' : c ≤ 1)
    (front : Fin H → ℝ) (hf : StrictMono front)
    (hfront : ∀ i, 0 < front i ∧ front i < c ∧ P (-front i) = 0 ∧
      0 < (-1:ℝ)^(i.val+2)*Q (-front i))
    (middle : Fin (n/2-(H+1)) → ℝ) (hm : StrictMono middle)
    (hmiddle : ∀ i, c < middle i ∧ middle i < 1 ∧ P (-middle i) = 0 ∧
      0 < (-1:ℝ)^(H+1+i.val+1)*Q (-middle i)) :
    ∃ u : Fin ((n-2)/2) → ℝ, StrictMono u ∧ ∀ i,
      0 < u i ∧ u i < 1 ∧ P (-u i) = 0 ∧ 0 < (-1:ℝ)^(i.val+2)*Q (-u i) := by
  let tail (i : Fin ((n-2)/2)) (hi : ¬ i.val < H) : Fin (n/2-(H+1)) :=
    ⟨i.val-H, by have := i.isLt; omega⟩
  let u (i : Fin ((n-2)/2)) : ℝ :=
    if hi : i.val < H then front ⟨i.val,hi⟩ else middle (tail i hi)
  refine ⟨u,?_,?_⟩
  · intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hj : j.val < H
    · have hi := hij'.trans hj
      simp only [u,dif_pos hi,dif_pos hj]
      exact hf (show (⟨i.val,hi⟩ : Fin H) < ⟨j.val,hj⟩ from hij')
    · by_cases hi : i.val < H
      · simp only [u,dif_pos hi,dif_neg hj]
        exact ((hfront ⟨i.val,hi⟩).2.1).trans (hmiddle (tail j hj)).1
      · simp only [u,dif_neg hi,dif_neg hj]
        apply hm
        change i.val-H < j.val-H
        omega
  · intro i
    by_cases hi : i.val < H
    · simp only [u,dif_pos hi]
      obtain ⟨hp,hu,hz,hs⟩ := hfront ⟨i.val,hi⟩
      exact ⟨hp,hu.trans_le hc',hz,hs⟩
    · simp only [u,dif_neg hi]
      obtain ⟨hp,hu,hz,hs⟩ := hmiddle (tail i hi)
      have he : H+1+(tail i hi).val+1 = i.val+2 := by dsimp [tail]; omega
      rw [he] at hs
      exact ⟨hc.trans hp,hu,hz,hs⟩

#print axioms join_signed_root_moduli
end OpenMathResearch.LongCycleExcedances
