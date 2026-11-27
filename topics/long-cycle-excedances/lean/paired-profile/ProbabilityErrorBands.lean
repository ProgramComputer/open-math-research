import FactorialProbabilityTail

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.CycleProbability

/-- The row of the rational error table selected by a lower bound on the
number of complete cutoff blocks. -/
def centeredErrorBound (j : ℕ) : ℝ :=
  if j=0 then 4/7 else if j=1 then 453/1000 else
    min (4/7 - if j=2 then 1/2 else 547/1000) (((j:ℝ)+1)/(2*(j:ℝ)*j.factorial))

theorem probability_error_bands {m N j : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d) (hk : 100 ≤ m+1)
    (hN : j*(m+1) ≤ N) :
    ((m:ℝ)+1)*|cutoffWeight (m+1) d N - Real.exp (-cycleHarmonic m)| ≤ centeredErrorBound j := by
  let K : ℝ := (m:ℝ)+1
  let C := Real.exp (-cycleHarmonic m)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨hc0,hc1⟩ := probability_limit_band hd hk
  change 548/1000 ≤ K*C at hc0
  change K*C ≤ 4/7 at hc1
  by_cases hn : m+1 ≤ N
  · simp only [cutoffWeight,if_pos hn]
    have hu := (hd.reciprocal_bounds (by omega) hn).2
    have hu' : K*d N ≤ 1 := by
      have hs : d N ≤ 1/K := by simpa [K] using hu
      simpa only [mul_comm] using (le_div_iff₀ hK).mp hs
    have hl : 1/2 < K*d N := by simpa [K] using lower_half hd (by omega) N hn
    have hsm : K*|d N-C| ≤ 453/1000 := by
      rw [←abs_of_pos hK,←abs_mul, mul_sub, abs_le]
      constructor
      · exact (by norm_num : -(453/1000:ℝ) ≤ 1/2 - 4/7).trans (sub_le_sub hl.le hc1)
      · exact (sub_le_sub hu' hc0).trans (by norm_num)
    by_cases h0 : j=0
    · simpa only [centeredErrorBound,if_pos h0] using hsm.trans (by norm_num : (453/1000:ℝ) ≤ 4/7)
    by_cases h1 : j=1
    · simpa only [centeredErrorBound,if_neg h0,if_pos h1] using hsm
    have hj : 2 ≤ j := by omega
    have hf := probability_factorial_tail hd hj hN
    rw [abs_sub_comm] at hf
    simp only [centeredErrorBound,if_neg h0,if_neg h1,le_min_iff]
    refine ⟨?_,hf⟩
    have h2 : 2*(m+1) ≤ N := (Nat.mul_le_mul_right (m+1) hj).trans hN
    have hu2 : K*d N ≤ 4/7 := by simpa [K] using upper47 hd hk N h2
    change K*|d N-C| ≤ _
    rw [←abs_of_pos hK,←abs_mul,mul_sub,abs_le]
    by_cases hj2 : j=2
    · rw [if_pos hj2]; constructor <;> linarith
    · have h3 : 3*(m+1) ≤ N := (Nat.mul_le_mul_right (m+1) (show 3 ≤ j by omega)).trans hN
      have hl3 : 548/1000 < K*d N := by simpa [K] using lower548 hd (by omega) N h3
      rw [if_neg hj2]; constructor <;> linarith
  · have h0 : j=0 := by
      cases j with
      | zero => rfl
      | succ i =>
        rw [Nat.succ_mul] at hN
        omega
    simp only [cutoffWeight,if_neg hn,zero_sub,abs_neg,abs_of_pos (Real.exp_pos _),
      centeredErrorBound,if_pos h0]
    exact hc1

#print axioms probability_error_bands
end OpenMathResearch.LongCycleExcedances.CycleProbability
