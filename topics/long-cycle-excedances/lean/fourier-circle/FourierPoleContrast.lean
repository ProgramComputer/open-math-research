import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- For a normalized odd pole Z = C + i m S, the two principal locations |m|=1
give equality in the squared calculation, and every larger height satisfies the
same contrast bound. -/
theorem normalized_lattice_contrast {C S m : ℝ} (h : C^2+S^2=1) (hS : 0 ≤ S) (hm : 1 ≤ |m|) :
    ‖1/(⟨C,m*S⟩:ℂ)-(C:ℂ)‖ ≤ |m| * S := by
  let z : ℂ := ⟨C,m*S⟩
  have hs : ‖z‖^2 = C^2 + m^2*S^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp only [z]
    ring
  have hm2 : 1 ≤ m^2 := by nlinarith [sq_abs m,sq_nonneg (|m|-1)]
  have hm4 : 1 ≤ m^2*m^2 := one_le_mul_of_one_le_of_one_le hm2 hm2
  have hz : z ≠ 0 := by
    intro e
    rw [e,norm_zero,zero_pow (by decide : 2≠0)] at hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hm2) (sq_nonneg S)]
  have hd : 1/z-(C:ℂ)=(1-(C:ℂ)*z)/z := by field_simp [hz] <;> ring
  have hn : ‖1-(C:ℂ)*z‖^2 = (1-C^2)^2+C^2*m^2*S^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z,Complex.mul_re,Complex.mul_im]
    ring
  change ‖1/z-(C:ℂ)‖ ≤ _
  rw [hd,norm_div,div_le_iff₀ (norm_pos_iff.mpr hz)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _) hS) (norm_nonneg _))).mp
  rw [hn,mul_pow,mul_pow,sq_abs,hs,show 1-C^2=S^2 by linarith]
  nlinarith [mul_nonneg (sub_nonneg.mpr hm4) (sq_nonneg (S^2))]

#print axioms normalized_lattice_contrast
end OpenMathResearch.LongCycleExcedances
