import NonprincipalPoleValue

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Finset CycleProbability
open scoped ComplexConjugate

private theorem principal_power_phase (m : ℕ) (θ : ℝ) :
    (pairedPoleDenom (cos θ) (sin θ) 0)^m =
      (cos ((m:ℝ)*θ):ℂ)+Complex.I*(sin ((m:ℝ)*θ):ℂ) := by
  induction m with
  | zero => simp
  | succ j ih =>
    rw [pow_succ,ih,show ((j+1:ℕ):ℝ)*θ=(j:ℝ)*θ+θ by push_cast; ring,Real.cos_add,Real.sin_add]
    simp only [pairedPoleDenom,Int.cast_zero,mul_zero,zero_add,mul_one,Complex.ofReal_sub,
      Complex.ofReal_mul,Complex.ofReal_add]
    linear_combination ((sin ((j:ℝ)*θ):ℂ)*(sin θ:ℂ)) * Complex.I_sq

theorem principal_phase_cancellation (n t : ℕ) (ht : t ≤ n+1) (θ : ℝ) (hS : 0 < sin θ) :
    let w := pairedPoleDenom (cos θ) (sin θ) 0
    w⁻¹^(n+1-t)*(w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ))=(sin θ:ℂ)*w^t := by
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  have hw : w≠0 := pairedPoleDenom_ne_zero _ hS.ne' _
  have ha : ((n+1:ℕ):ℝ)*θ=(n:ℝ)*θ+θ := by push_cast; ring
  have hφ : w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ) = (sin θ:ℂ)*w^(n+1) := by
    rw [show w=pairedPoleDenom (cos θ) (sin θ) 0 from rfl,
      angular_pole_sine_difference,principal_power_phase,ha]
    simp [primitiveOddNumber]
  change w⁻¹^(n+1-t)*(w*_ - _) = (sin θ:ℂ)*w^t
  rw [hφ,show w^(n+1)=w^(n+1-t)*w^t by rw [←pow_add,Nat.sub_add_cancel ht],inv_pow]
  field_simp [hw] <;> ring

#print axioms principal_phase_cancellation
end OpenMathResearch.LongCycleExcedances
