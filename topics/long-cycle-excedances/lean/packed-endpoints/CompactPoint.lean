import PositiveCeilHorner
import IntegerTail

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open Polynomial Finset

/-- A packed prefix keeps natural coefficients; the signed Horner accumulator is an integer. -/
def packedPointCheck (n W : ℕ) (c : ℕ → ℤ) (p : ℤ) (D : ℕ) (s : ℤ) : Bool :=
  let U := ((W:ℤ)+1)^n
  let V := ((W:ℤ)+2)^n
  let Z := (D:ℤ)*U-p*V
  let cs := firstCoeffs c W
  let M := s*roundedRatio p D cs-2-uncertainty p D cs
  decide (0<D ∧ 0≤p ∧ 2*p≤(D:ℤ) ∧ (s=1 ∨ s= -1) ∧
    0<Z ∧ (D:ℤ)*U^2*p^W < M*(D:ℤ)^W*Z)

theorem original_signed_of_packed_margin (n k W : ℕ) (hk : 2 ≤ k) (c : ℕ → ℤ)
    (p : ℤ) (D : ℕ) (s : ℤ) (ok : packedPointCheck n W c p D s = true)
    (enclosure : let y := (((p:ℚ)/D : ℚ):ℝ)
      |prefixEval (canonicalReducedRow n k) W y - ∑ i ∈ range W, (c i : ℝ)*(-y)^i| ≤
        (1/(2:ℝ)^36)*∑ i ∈ range W, (c i : ℝ)*y^i) :
    0 < (s:ℝ)*(canonicalReducedRow n k).eval (-(((p:ℚ)/D : ℚ):ℝ)) := by
  unfold packedPointCheck at ok
  obtain ⟨hd,hp,hpD,hs,hz,hm⟩ := of_decide_eq_true ok
  obtain ⟨hq,hm'⟩ := integer_tail_margin n W D p _ hd hz hm
  have hD : (0:ℚ) < D := by exact_mod_cast hd
  have hy : 0 ≤ (p:ℚ)/D := div_nonneg (by exact_mod_cast hp) hD.le
  have hu : (p:ℚ)/D ≤ 1/2 := by
    apply (div_le_iff₀ hD).2
    have h : 2*(p:ℚ) ≤ D := by exact_mod_cast hpD
    linarith
  have hσ : |(s:ℚ)|=1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  let y := ((p:ℚ)/D : ℚ)
  apply signed_eval_pos_of_prefix_margin _ n W (by exact_mod_cast hy) le_rfl
  · rw [← rationalTailRatio_cast]
    exact_mod_cast hq
  · exact fun i _ => canonical_coeff_envelope n k i hk
  · exact_mod_cast hσ
  · rw [← rationalTailBound_cast]
    refine lt_of_lt_of_le ?_ (compressed_integer_margin p s D W c hy hu hσ _ enclosure)
    exact_mod_cast hm'

#print axioms original_signed_of_packed_margin
end OpenMathResearch.LongCycleExcedances.IntegerSign
