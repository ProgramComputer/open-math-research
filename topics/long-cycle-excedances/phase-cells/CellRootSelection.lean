import AngularGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

private def argValue (u : ℝ) : ℝ := -exp (-angleCoordinate u)

private theorem argValue_antitone : StrictAntiOn argValue (Ioo 0 (π/2)) := by
  intro a ha b hb hab
  have haπ : a < π := by linarith [ha.2, pi_pos]
  have hbπ : b < π := by linarith [hb.2, pi_pos]
  have hsa := sin_pos_of_pos_of_lt_pi ha.1 haπ
  have hsb := sin_pos_of_pos_of_lt_pi hb.1 hbπ
  have hcos := strictAntiOn_cos ⟨ha.1.le,haπ.le⟩ ⟨hb.1.le,hbπ.le⟩ hab
  have hsin := strictMonoOn_sin ⟨by linarith [ha.1,pi_pos],ha.2.le⟩
    ⟨by linarith [hb.1,pi_pos],hb.2.le⟩ hab
  have hcb : 0 < cos b := cos_pos_of_mem_Ioo ⟨by linarith [hb.1,pi_pos],hb.2⟩
  have hquot : cos b/sin b < cos a/sin a := by
    apply (div_lt_div_iff₀ hsb hsa).2
    exact (mul_lt_mul_of_pos_left hsin hcb).trans (mul_lt_mul_of_pos_right hcos hsb)
  exact neg_lt_neg (exp_lt_exp.mpr (neg_lt_neg (mul_lt_mul_of_pos_left hquot pi_pos)))

/-- Select strictly decreasing negative roots from disjoint complete angular cells.
The values of the next polynomial are signed at these original roots. -/
theorem ordered_grid_roots (P Q : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (cells : ∀ j : ℕ, π/6 ≤ (j:ℝ)*π/n → ((j+1:ℕ):ℝ)*π/n ≤ π/2 →
      ∃ θ ∈ Ioo ((j:ℝ)*π/n) (((j+1:ℕ):ℝ)*π/n),
        P (-exp (-angleCoordinate θ)) = 0 ∧
          0 < (-1:ℝ)^(j+1) * Q (-exp (-angleCoordinate θ))) :
    ∃ z : Fin (n/2 - (n+5)/6) → ℝ, StrictAnti z ∧
      ∀ i, z i ∈ Ioo (-1:ℝ) 0 ∧ P (z i) = 0 ∧
        0 < (-1:ℝ)^((n+5)/6 + i.val + 1) * Q (z i) := by
  let j (i : Fin (n/2 - (n+5)/6)) := (n+5)/6 + i.val
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have left (i) : π/6 ≤ (j i:ℝ)*π/n := by
    have hi : n ≤ 6*(j i) := by dsimp [j]; omega
    have h : (n:ℝ) ≤ 6*(j i:ℝ) := by exact_mod_cast hi
    apply (le_div_iff₀ hn').2
    nlinarith [mul_le_mul_of_nonneg_right h pi_pos.le]
  have right (i) : ((j i+1:ℕ):ℝ)*π/n ≤ π/2 := by
    have hi := i.isLt
    have hh : 2*(j i+1) ≤ n := by dsimp [j]; omega
    have h : 2*((j i+1:ℕ):ℝ) ≤ n := by exact_mod_cast hh
    apply (div_le_iff₀ hn').2
    nlinarith [mul_le_mul_of_nonneg_right h pi_pos.le]
  choose θ hθ hroot hsign using fun i => cells (j i) (left i) (right i)
  have band (i) : θ i ∈ Ioo 0 (π/2) :=
    ⟨(show 0 < π/6 by linarith [pi_pos]).trans ((left i).trans_lt (hθ i).1),
      (hθ i).2.trans_le (right i)⟩
  refine ⟨fun i => argValue (θ i), ?_, ?_⟩
  · intro i l hil
    apply argValue_antitone (band i) (band l)
    have hj : j i + 1 ≤ j l := by dsimp [j]; have := Fin.lt_iff_val_lt_val.mp hil; omega
    have hcast : ((j i+1:ℕ):ℝ) ≤ (j l:ℝ) := by exact_mod_cast hj
    exact (hθ i).2.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast pi_pos.le)
      hn'.le).trans_lt (hθ l).1)
  · intro i
    have hu := band i
    have hs := sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2,pi_pos])
    have hc : 0 < cos (θ i) := cos_pos_of_mem_Ioo ⟨by linarith [hu.1,pi_pos],hu.2⟩
    have hx : 0 < angleCoordinate (θ i) := mul_pos pi_pos (div_pos hc hs)
    refine ⟨⟨?_, neg_neg_of_pos (exp_pos _)⟩, hroot i, hsign i⟩
    exact neg_lt_neg (exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))

#print axioms ordered_grid_roots
end OpenMathResearch.LongCycleExcedances
