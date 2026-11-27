import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

/-- Consecutive integer phase levels select ordered roots in logarithmic
coordinates, with the sign of the larger row at each selected root. -/
theorem ordered_middle_level_roots (P Q φ : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (L M : ℕ) (hφcont : ContinuousOn φ (Icc 0 b)) (hφ : StrictAntiOn φ (Icc 0 b))
    (hlo : φ b < (L:ℝ)*π) (hhi : (M:ℝ)*π ≤ φ 0)
    (cell : ∀ (j : ℕ) {u v : ℝ}, 0 ≤ u → u < v → v ≤ b →
      φ u = ((j+1:ℕ):ℝ)*π → φ v = (j:ℝ)*π →
      ∃ x ∈ Ioo u v, P (-exp (-x)) = 0 ∧
        0 < (-1:ℝ)^(j+1) * Q (-exp (-x))) :
    ∃ z : Fin (M-L) → ℝ, StrictAnti z ∧
      ∀ i, z i ∈ Ioo (-1:ℝ) (-exp (-b)) ∧ P (z i) = 0 ∧
        0 < (-1:ℝ)^(L+i.val+1) * Q (z i) := by
  let j (i : Fin (M-L)) := L+i.val
  have level (q : ℕ) (hl : L ≤ q) (hq : q ≤ M) :
      ∃ x ∈ Icc 0 b, φ x = (q:ℝ)*π := by
    have hl' : (L:ℝ) ≤ q := by exact_mod_cast hl
    have hq' : (q:ℝ) ≤ M := by exact_mod_cast hq
    exact intermediate_value_Icc' hb hφcont
      ⟨hlo.le.trans (mul_le_mul_of_nonneg_right hl' pi_pos.le),
        (mul_le_mul_of_nonneg_right hq' pi_pos.le).trans hhi⟩
  have inside (i : Fin (M-L)) :
      ∃ x ∈ Ioo 0 b, (j i:ℝ)*π < φ x ∧ φ x < ((j i+1:ℕ):ℝ)*π ∧
        P (-exp (-x)) = 0 ∧ 0 < (-1:ℝ)^(j i+1) * Q (-exp (-x)) := by
    have hL : L ≤ j i := by dsimp [j]; omega
    have hM : j i+1 ≤ M := by dsimp [j]; have := i.isLt; omega
    obtain ⟨u, hu, hfu⟩ := level (j i+1) (by omega) hM
    obtain ⟨v, hv, hfv⟩ := level (j i) hL (by omega)
    have huv : u < v := by
      by_contra! h
      have hp := hφ.antitoneOn hv hu h
      rw [hfu, hfv, Nat.cast_succ, add_mul, one_mul] at hp
      linarith only [hp, pi_pos]
    obtain ⟨x, hx, hr, hs⟩ := cell (j i) hu.1 huv hv.2 hfu hfv
    have hxb : x ∈ Ioo 0 b := ⟨hu.1.trans_lt hx.1, hx.2.trans_le hv.2⟩
    have hxC : x ∈ Icc 0 b := ⟨hxb.1.le, hxb.2.le⟩
    refine ⟨x, hxb, ?_, ?_, hr, hs⟩
    · rw [←hfv]
      exact hφ hxC hv hx.2
    · rw [←hfu]
      exact hφ hu hxC hx.1
  choose x hx hlo' hhi' hroot hsign using inside
  have ht : StrictMono (fun y : ℝ => -exp (-y)) :=
    fun _ _ h => neg_lt_neg (exp_lt_exp.mpr (neg_lt_neg h))
  refine ⟨fun i => -exp (-x i), ?_, ?_⟩
  · intro i a hia
    apply ht
    by_contra! h
    have hi := Fin.lt_iff_val_lt_val.mp hia
    have hj : j i+1 ≤ j a := by dsimp [j]; omega
    have hj' : ((j i+1:ℕ):ℝ) ≤ (j a:ℝ) := by exact_mod_cast hj
    have hphase := (hhi' i).trans_le (mul_le_mul_of_nonneg_right hj' pi_pos.le)
    exact (not_lt_of_ge (hφ.antitoneOn ⟨(hx i).1.le, (hx i).2.le⟩
      ⟨(hx a).1.le, (hx a).2.le⟩ h)) (hphase.trans (hlo' a))
  · intro i
    have hp : -exp (-(0:ℝ)) < -exp (-x i) := ht (hx i).1
    rw [neg_zero, exp_zero] at hp
    exact ⟨⟨hp, ht (hx i).2⟩, hroot i, hsign i⟩

#print axioms ordered_middle_level_roots
end OpenMathResearch.LongCycleExcedances
