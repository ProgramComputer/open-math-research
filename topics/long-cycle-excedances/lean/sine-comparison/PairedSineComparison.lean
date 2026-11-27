import PairedIntegerWindows

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The adjacent-row comparison with the unshifted sine sequence. -/
def pairedSineDifference (n : ℕ) (z P Q : ℝ) : ℝ :=
  sin (((n:ℝ)+1)*z)*P - sin ((n:ℝ)*z)*Q

theorem paired_sine_sample {n j : ℕ} {z P Q : ℝ} (hz : 0 < sin z)
    (hphase : (n:ℝ)*z = (j:ℝ)*π) (h : 0 < pairedSineDifference n z P Q) :
    0 < (-1:ℝ)^j*P := by
  have hcos : cos ((j:ℝ)*π) = (-1:ℝ)^j := by simpa using cos_add_nat_mul_pi 0 j
  simp only [pairedSineDifference,add_mul,one_mul,hphase,sin_add,sin_nat_mul_pi,hcos,
    zero_mul,zero_add,sub_zero] at h
  rw [mul_comm ((-1:ℝ)^j) (sin z),mul_assoc] at h
  exact pos_of_mul_pos_right h hz.le

theorem paired_sine_at_root {n j : ℕ} {z Q : ℝ}
    (hlo : (j:ℝ)*π < (n:ℝ)*z) (hhi : (n:ℝ)*z < ((j:ℝ)+1)*π)
    (h : 0 < pairedSineDifference n z 0 Q) : 0 < (-1:ℝ)^(j+1)*Q := by
  let u := (n:ℝ)*z - (j:ℝ)*π
  have hu : 0 < sin u := sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlo)
    (by dsimp only [u]; linarith only [hhi])
  have hcos : cos ((j:ℝ)*π) = (-1:ℝ)^j := by simpa using cos_add_nat_mul_pi 0 j
  have he : sin ((n:ℝ)*z) = sin u * (-1:ℝ)^j := by
    calc
      _ = sin (u+(j:ℝ)*π) := by dsimp only [u]; rw [sub_add_cancel]
      _ = _ := by rw [sin_add,sin_nat_mul_pi,hcos,mul_zero,add_zero]
  rw [pairedSineDifference,mul_zero,zero_sub,he] at h
  have hh : -(sin u*(-1:ℝ)^j*Q) = sin u*((-1:ℝ)^(j+1)*Q) := by rw [pow_succ]; ring
  exact pos_of_mul_pos_right (hh ▸ h) hu.le

/-- Exact comparison on a principal conjugate pair with an arbitrary
complex multiplier represented by its real and imaginary parts. -/
theorem paired_sine_principal (n : ℕ) (z A B : ℝ) :
    pairedSineDifference n z (A*cos ((n:ℝ)*z)+B*sin ((n:ℝ)*z))
      (A*cos (((n:ℝ)+1)*z)+B*sin (((n:ℝ)+1)*z)) = A*sin z := by
  simp only [pairedSineDifference,add_mul,one_mul,sin_add,cos_add]
  linear_combination A*sin z*(sin_sq_add_cos_sq ((n:ℝ)*z))

#print axioms paired_sine_sample
#print axioms paired_sine_at_root
#print axioms paired_sine_principal
end OpenMathResearch.LongCycleExcedances
