import JoinAngle

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The entrance to the middle-root phase is already above the log-tilt
height cutoff once the old size is at least 25 times the cutoff. -/
theorem wide_join_cutoff_separation {n k : ℕ} (hn : 10000 ≤ n) (hx : 25*k ≤ n) :
    10*sqrt (k:ℝ) < uniformJoinLog n := by
  have h : 25*(k:ℝ) ≤ n := by exact_mod_cast hx
  have hs := Real.sqrt_le_sqrt h
  have h25 : sqrt (25:ℝ)=5 := by
    rw [show (25:ℝ)=5^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤25),h25] at hs
  exact (by linarith only [hs] : 10*sqrt (k:ℝ) ≤ 2*sqrt (n:ℝ)).trans_lt
    (uniform_join_geometry hn).2.2.2.1

#print axioms wide_join_cutoff_separation
end OpenMathResearch.LongCycleExcedances
