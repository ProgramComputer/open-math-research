import PrincipalAdjacentError
import ProbabilityErrorBands

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability Finset

/-- Bound the literal old-row convolution error by nonnegative degree
masses after multiplication by the cutoff, including every omitted degree. -/
theorem centered_principal_cost {m n : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d) (hk : 100 ≤ m+1)
    {Q : PowerSeries ℂ} {w value : ℂ} (hQ : CoeffHasSum Q w value)
    (j : ℕ→ℕ) (hj : ∀ t, j t*(m+1) ≤ n-t)
    {g : ℕ→ℝ} {E : ℝ} (hsum : HasSum g E)
    (hg : ∀ t, centeredErrorBound (j t)*‖PowerSeries.coeff (R := ℂ) t Q*w^t‖ ≤ g t) :
    ‖((m:ℝ)+1:ℂ)*((∑ t ∈ range (n+1),
       (cutoffWeight (m+1) d (n-t):ℂ)*(PowerSeries.coeff (R := ℂ) t Q*w^t)) -
        (Real.exp (-cycleHarmonic m):ℂ)*value)‖ ≤ E := by
  let p (s:ℕ) : ℂ := (cutoffWeight (m+1) d s:ℂ)
  let c := Real.exp (-cycleHarmonic m)
  have he := (principal_error_hasSum hQ p (c:ℂ) n).mul_left ((m:ℝ)+1:ℂ)
  apply he.norm_le_of_bounded hsum
  intro t
  have heq : zeroLeft p n t = p (n-t) := by
    by_cases ht : t ≤ n
    · simp [zeroLeft,ht]
    · simp [zeroLeft,ht,Nat.sub_eq_zero_of_le (le_of_not_ge ht),p,cutoffWeight]
  rw [heq]
  have hb := probability_error_bands hd hk (hj t)
  calc
    _ = (((m:ℝ)+1)*|cutoffWeight (m+1) d (n-t)-c|)*‖PowerSeries.coeff (R := ℂ) t Q*w^t‖ := by
      rw [norm_mul,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have hr : ‖((m:ℝ)+1:ℂ)‖ = (m:ℝ)+1 := by
        rw [show ((m:ℝ)+1:ℂ)=(((m:ℝ)+1:ℝ):ℂ) by push_cast; rfl,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rw [hr,mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (hg t)

#print axioms centered_principal_cost
end OpenMathResearch.LongCycleExcedances
