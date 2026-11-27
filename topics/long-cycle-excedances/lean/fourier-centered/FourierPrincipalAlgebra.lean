import EnclosedPolePairing
import FourierContourReadout

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

/-- Principal inverse direction has cosine s/r and imaginary part −π/r. -/
theorem actual_principal_displacement (s : ℝ) :
    let p := fourierRowPole s 0
    let r := ‖p‖
    (r:ℂ)/p-(s/r:ℝ)= -((π/r:ℝ):ℂ)*Complex.I := by
  intro p r
  have hre : p.re=s := by simp [p,fourierRowPole]
  have him : p.im=π := by simp [p,fourierRowPole]
  have hr : 0 < r := Real.pi_pos.trans_le (him ▸ (le_abs_self p.im).trans (Complex.abs_im_le_norm p))
  have hsq : p.normSq = r^2 := (Complex.sq_norm p).symm
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.ofReal_re,Complex.div_re,Complex.ofReal_im,zero_mul,
      zero_div,add_zero,Complex.mul_I_re,Complex.neg_im,neg_zero,hre,hsq]
    field_simp [hr.ne']; ring
  · simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.div_im,zero_mul,
      zero_div,zero_sub,Complex.mul_I_im,Complex.neg_re,Complex.ofReal_re,him,hsq]
    field_simp [hr.ne']; ring

/-- Conjugation of both the normalized original residue and the signed
adjacent correction follows from a real numerator. -/
theorem normalized_residue_conjugation (N : ℂ → ℂ) (hN : ∀ w, N ((starRingEnd ℂ) w)=(starRingEnd ℂ) (N w))
    (n : ℕ) (r U C : ℝ) (w : ℂ) :
    let b := fun z : ℂ => (N z/(U:ℂ))*((r:ℂ)/z)^(n+1)
    let d := fun z : ℂ => ((r:ℂ)/z-(C:ℂ))*b z
    b ((starRingEnd ℂ) w)=(starRingEnd ℂ) (b w) ∧ d ((starRingEnd ℂ) w)=(starRingEnd ℂ) (d w) := by
  simp only [hN,map_mul,map_pow,map_div₀,map_sub,Complex.conj_ofReal,and_self]

#print axioms actual_principal_displacement
#print axioms normalized_residue_conjugation
end OpenMathResearch.LongCycleExcedances
