import FourierMinorSum
import LiteralDiscretePoleMoments

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset

/-- The selected squared-radius cap at height zero lies strictly below the
first nonprincipal pole. The positive-height estimate thus extends to the
closed angular sector, including its central endpoint. -/
theorem minor_window_at_zero {k : ℕ} (hk : 100 ≤ k) {R : ℝ}
    (hcap : R^2 ≤ ‖numeratorPole 0 0‖^2*(1+2/(k:ℝ)))
    (I : Finset ℕ) (henc : ∀ i ∈ I, ‖numeratorPole 0 ((i+1:ℕ):ℤ)‖ ≤ R) : I=∅ := by
  have hK : (100:ℝ) ≤ k := by exact_mod_cast hk
  have hK' : (0:ℝ)<k := by linarith
  have hp (l : ℤ) (hl : 0 ≤ l) : ‖numeratorPole 0 l‖=(2*(l:ℝ)+1)*π := by
    have hl' : (0:ℝ) ≤ l := by exact_mod_cast hl
    have h := literal_pole_norm_sq 0 l
    simp only [zero_pow (by decide : 2≠0),zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) (by decide : 2≠0)).mp h
  rw [hp 0 (by decide)] at hcap
  norm_num at hcap
  apply empty_minor_window pi_pos (s:=I) (w:=fun i => numeratorPole 0 ((i+1:ℕ):ℤ)) _ _ henc
  · apply hcap.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith only [(div_le_one hK').2 (by linarith : (2:ℝ) ≤ k)]
  · intro i
    rw [hp _ (by positivity)]
    apply mul_le_mul_of_nonneg_right _ pi_pos.le
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) i]

/-- In the old row the extra radial factor contracts for all nonprincipal
poles, uniformly in height. -/
theorem principal_radius_le_minor (s : ℝ) (i : ℕ) :
    ‖numeratorPole s 0‖ ≤ ‖numeratorPole s ((i+1:ℕ):ℤ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [literal_pole_norm_sq,literal_pole_norm_sq]
  simp only [Int.cast_zero,mul_zero,zero_add,one_mul]
  apply add_le_add_left
  apply (sq_le_sq₀ pi_pos.le (by positivity)).mpr
  calc
    π = 1*π := (one_mul _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ pi_pos.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) i]

#print axioms minor_window_at_zero
#print axioms principal_radius_le_minor
end OpenMathResearch.LongCycleExcedances
