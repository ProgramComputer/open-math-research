import ReciprocalWindowSigns

namespace OpenMathResearch.LongCycleExcedances
open Polynomial

/-- Reflect ordered brackets below modulus one to the upper half-axis. For
odd old degree the only additional witness is the next sign at modulus one. -/
theorem mixed_witnesses_of_reciprocal_half {d : ℕ} {P Q : ℝ[X]}
    (hP : ∀ t : ℝ, t ≠ 0 → t^d * P.eval t⁻¹ = P.eval t)
    (hQ : ∀ t : ℝ, t ≠ 0 → t^(d+1) * Q.eval t⁻¹ = Q.eval t)
    (l u : Fin (d / 2) → ℝ)
    (hl : ∀ i, 0 < l i) (hu : ∀ i, u i < 1)
    (horder : ∀ i j, i < j → u i < l j)
    (hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ P.eval (-l i) * P.eval (-u i) < 0))
    (hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i))
    (hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i))
    (hcenter : Odd d → 0 < (-1 : ℝ) ^ (d / 2 + 1) * Q.eval (-1)) :
    ∃ L U : Fin d → ℝ, (∀ i, 0 < L i) ∧ (∀ i j, i < j → U i < L j) ∧
      (∀ i, (L i = U i ∧ P.IsRoot (-L i)) ∨
        (L i < U i ∧ P.eval (-L i) * P.eval (-U i) < 0)) ∧
      (∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-L i)) ∧
      (∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-U i)) := by
  let L (i : Fin d) : ℝ :=
    if h : i.val < d / 2 then l ⟨i.val, h⟩
    else if h : i.rev.val < d / 2 then (u ⟨i.rev.val, h⟩)⁻¹
    else 1
  let U (i : Fin d) : ℝ :=
    if h : i.val < d / 2 then u ⟨i.val, h⟩
    else if h : i.rev.val < d / 2 then (l ⟨i.rev.val, h⟩)⁻¹
    else 1
  have hleft (i : Fin d) (hi : i.val < d / 2) :
      L i = l ⟨i.val, hi⟩ ∧ U i = u ⟨i.val, hi⟩ := by simp [L, U, hi]
  have hright (i : Fin d) (hi : i.rev.val < d / 2) :
      L i = (u ⟨i.rev.val, hi⟩)⁻¹ ∧ U i = (l ⟨i.rev.val, hi⟩)⁻¹ := by
    have hn : ¬ i.val < d / 2 := by
      have := i.isLt
      simp only [Fin.val_rev] at hi
      omega
    simp only [L, U, dif_neg hn, dif_pos hi, and_self]
  have hmid (i : Fin d) (hi : ¬ i.val < d / 2) (hj : ¬ i.rev.val < d / 2) :
      L i = 1 ∧ U i = 1 ∧ i.val = d / 2 ∧ Odd d := by
    have := i.isLt
    simp only [Fin.val_rev] at hj
    refine ⟨by simp [L, hi, hj, Fin.val_rev], by simp [U, hi, hj, Fin.val_rev], by omega, ?_⟩
    exact ⟨d / 2, by omega⟩
  have hle (i : Fin (d / 2)) : l i ≤ u i :=
    (hold i).elim (fun h => h.1.le) (fun h => h.1.le)
  have huPos (i : Fin (d / 2)) : 0 < u i := (hl i).trans_le (hle i)
  have hafter (i : Fin d) (hi : ¬ i.val < d / 2) : 1 ≤ L i := by
    by_cases hir : i.rev.val < d / 2
    · rw [(hright i hir).1]
      exact ((one_lt_inv₀ (huPos _)).2 (hu _)).le
    · rw [(hmid i hi hir).1]
  refine ⟨L, U, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < d / 2
    · rw [(hleft i hi).1]
      exact hl _
    · exact zero_lt_one.trans_le (hafter i hi)
  · intro i j hij
    by_cases hi : i.val < d / 2
    · rw [(hleft i hi).2]
      by_cases hj : j.val < d / 2
      · rw [(hleft j hj).1]
        exact horder _ _ hij
      · exact (hu _).trans_le (hafter j hj)
    · have hj : ¬ j.val < d / 2 := by
        change i.val < j.val at hij
        omega
      have hrev : j.rev.val < i.rev.val := Fin.rev_lt_rev.mpr hij
      have hjr : j.rev.val < d / 2 := by
        by_contra hjr
        have hir : ¬ i.rev.val < d / 2 := fun hir => hjr (hrev.trans hir)
        have hiMid := (hmid i hi hir).2.2.1
        have hjMid := (hmid j hj hjr).2.2.1
        change i.val < j.val at hij
        omega
      rw [(hright j hjr).1]
      by_cases hir : i.rev.val < d / 2
      · rw [(hright i hir).2]
        exact (inv_lt_inv₀ (hl _) (huPos _)).2 (horder _ _ hrev)
      · rw [(hmid i hi hir).2.1]
        exact (one_lt_inv₀ (huPos _)).2 (hu _)
  · intro i
    by_cases hi : i.val < d / 2
    · rw [(hleft i hi).1, (hleft i hi).2]
      exact hold _
    · by_cases hir : i.rev.val < d / 2
      · rw [(hright i hir).1, (hright i hir).2]
        let j : Fin (d / 2) := ⟨i.rev.val, hir⟩
        rcases hold j with ⟨heq, hroot⟩ | ⟨hwidth, hprod⟩
        · exact Or.inl ⟨congrArg Inv.inv heq.symm,
            heq ▸ (reciprocal_root_of_root hP (hl j) hroot)⟩
        · exact Or.inr ⟨(inv_lt_inv₀ (huPos j) (hl j)).2 hwidth,
            reciprocal_opposite_signs hP (hl j) (huPos j) hprod⟩
      · obtain ⟨hl', hu', _, hodd⟩ := hmid i hi hir
        rw [hl', hu']
        exact Or.inl ⟨rfl, reciprocal_center_root_of_odd hP hodd⟩
  · have hsigns (i : Fin d) :
        0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-L i) ∧
          0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-U i) := by
      by_cases hi : i.val < d / 2
      · rw [(hleft i hi).1, (hleft i hi).2]
        exact ⟨hsLeft ⟨i.val, hi⟩, hsRight ⟨i.val, hi⟩⟩
      · by_cases hir : i.rev.val < d / 2
        · rw [(hright i hir).1, (hright i hir).2]
          have hsign := reflected_index_next_sign i.rev
          rw [Fin.rev_rev] at hsign
          rw [hsign]
          let j : Fin (d / 2) := ⟨i.rev.val, hir⟩
          exact ⟨reciprocal_signed_pos hQ (huPos j) (hsRight j),
            reciprocal_signed_pos hQ (hl j) (hsLeft j)⟩
        · obtain ⟨hlo, hup, heq, hodd⟩ := hmid i hi hir
          rw [hlo, hup, heq]
          exact ⟨hcenter hodd, hcenter hodd⟩
    exact ⟨fun i => (hsigns i).1, fun i => (hsigns i).2⟩

#print axioms mixed_witnesses_of_reciprocal_half
end OpenMathResearch.LongCycleExcedances
