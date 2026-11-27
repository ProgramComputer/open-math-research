import PairedCycleNormalization

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

def scaledCycleLog (R : ℝ) (M : ℕ → ℝ) (k : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun p => if k ≤ p then (R:ℂ)^p*(M p:ℂ)/(p.factorial:ℂ) else 0

/-- The factorial-scaled profile is the corresponding ordinary coefficient.
The two recurrence hypotheses are exactly the frozen orderedMomentRow equations. -/
theorem coeff_pow_eq_scaled_ordered_profile (R : ℝ) (M : ℕ → ℝ) (k : ℕ)
    (A : ℕ → ℕ → ℝ) (h0 : ∀ n, A n 0 = if n=0 then 1 else 0)
    (hs : ∀ n h, A n (h+1) =
      ∑ p ∈ Icc k n, (n.choose p:ℝ)*M p*A (n-p) h) (n h : ℕ) :
    PowerSeries.coeff (R := ℂ) n (scaledCycleLog R M k ^ h) =
      (R:ℂ)^n*(A n h:ℂ)/(n.factorial:ℂ) := by
  induction h generalizing n with
  | zero =>
    by_cases hn : n=0
    · subst n
      simp [h0]
    · simp [PowerSeries.coeff_one, h0, hn]
  | succ h ih =>
    rw [pow_succ', PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hs]
    simp only [ih]
    simp only [scaledCycleLog, PowerSeries.coeff_mk, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_natCast]
    simp only [div_eq_mul_inv, mul_sum, sum_mul]
    rw [show Icc k n = (range (n+1)).filter (fun p => k ≤ p) by
      ext p
      simp
      omega]
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hkp : k ≤ p
    · simp only [if_pos hkp]
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hp)
      have hfac : (n.choose p:ℂ)*(p.factorial:ℂ)*((n-p).factorial:ℂ) =
          (n.factorial:ℂ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hpn
      have hpow : (R:ℂ)^p*(R:ℂ)^(n-p) = (R:ℂ)^n := by
        rw [← pow_add, Nat.add_sub_of_le hpn]
      have hf : (p.factorial:ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
      have hg : ((n-p).factorial:ℂ) ≠ 0 := by exact_mod_cast (n-p).factorial_ne_zero
      have hc : (n.choose p:ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hpn).ne'
      rw [← hfac, ← hpow]
      field_simp [hf, hg, hc] <;> ring
    · simp [hkp]

/-- The original profile weighting by 1/h! gives the truncated exponential. -/
theorem truncated_exp_eq_scaled_profile_sum (R : ℝ) (M : ℕ → ℝ) (k : ℕ)
    (A : ℕ → ℕ → ℝ) (h0 : ∀ n, A n 0 = if n=0 then 1 else 0)
    (hs : ∀ n h, A n (h+1) =
      ∑ p ∈ Icc k n, (n.choose p:ℝ)*M p*A (n-p) h) (n J : ℕ) :
    (∑ h ∈ range (J+1), PowerSeries.coeff (R := ℂ) n (scaledCycleLog R M k ^ h) /
      (h.factorial:ℂ)) =
      (R:ℂ)^n*((∑ h ∈ range (J+1), (1/(h.factorial:ℝ))*A n h : ℝ):ℂ)/
        (n.factorial:ℂ) := by
  simp only [coeff_pow_eq_scaled_ordered_profile R M k A h0 hs, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
    div_eq_mul_inv, mul_sum, sum_mul, Complex.ofReal_inv]
  apply sum_congr rfl
  intro h _
  ring

#print axioms truncated_exp_eq_scaled_profile_sum
#print axioms coeff_pow_eq_scaled_ordered_profile
end OpenMathResearch.LongCycleExcedances
