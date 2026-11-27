import UniformDiscreteTilt

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Scale the Eulerian moment at a pole before taking the absolute value.
This keeps the same dimensionless lattice sum for all logarithmic moduli. -/
theorem pole_monomial_bound {d : ℕ} (hd : 1 ≤ d) (m γ : ℝ) (hγ : 0 ≤ γ)
    (w : ℂ) (p : ℤ → ℂ)
    (moment : (m:ℂ) = (d-1).factorial * ∑' l, (1:ℂ)/p l^d)
    (hs : Summable fun l => ‖w/p l‖^d) :
    |(-m/(d.factorial:ℝ))*(‖w‖*γ)^d| ≤
      γ^d * (∑' l, ‖w/p l‖^d)/(d:ℝ) := by
  let f (l : ℤ) := (w/p l)^d
  have eqf : ∑' l, f l = w^d * ∑' l, (1:ℂ)/p l^d := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro l
    dsimp only [f]
    rw [div_pow,one_div,div_eq_mul_inv]
  have hs' : Summable fun l => ‖f l‖ := by simpa only [f,norm_pow] using hs
  have hn := norm_tsum_le_tsum_norm hs'
  rw [eqf,norm_mul,norm_pow] at hn
  simp only [f,norm_pow] at hn
  have hm := congrArg norm moment
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_natCast] at hm
  have hfac : d.factorial = d*(d-1).factorial := by
    cases d with
    | zero => omega
    | succ n => simp [Nat.factorial_succ]
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hcount : (0:ℝ) < (d-1).factorial := by positivity
  rw [mul_pow,abs_mul,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d.factorial),
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg hγ _)),hm,hfac,Nat.cast_mul]
  calc
    _ = γ^d*(‖w‖^d*‖∑' l, (1:ℂ)/p l^d‖)/(d:ℝ) := by field_simp [hd'.ne',hcount.ne'] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (pow_nonneg hγ _)) hd'.le

#print axioms pole_monomial_bound
end OpenMathResearch.LongCycleExcedances
