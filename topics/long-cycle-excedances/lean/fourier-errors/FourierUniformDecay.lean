import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- The two selected comparisons have the stronger radial decay at every aspect. -/
theorem selected_circle_decay {K r R a : ℝ} (hk : 100 ≤ K) (hr : 0 < r) (hR : 0 < R)
    (ha : 48/25 ≤ a) (ha2 : a ≤ 2) (hR2 : R^2=r^2*(1+a/K)) (n : ℕ) :
    (r/R)^n ≤ Real.exp (-(19/20)*((n:ℝ)/K)) := by
  have hK : 0 < K := by linarith
  have hz : 0 ≤ a/K := div_nonneg (by linarith) hK.le
  have hs : 0 < 1+a/K := by positivity
  have hlog := Real.le_log_one_add_of_nonneg hz
  have he : 19/10/K ≤ 2*(a/K)/(a/K+2) := by
    rw [div_le_div_iff₀ hK (by positivity)]
    have hsmall : a/K ≤ 2/100 := (div_le_iff₀ hK).mpr (by linarith)
    have hh : a/K*K = a := div_mul_cancel₀ _ hK.ne'
    nlinarith only [ha,hsmall,hh]
  have h1 := congrArg Real.log hR2
  rw [Real.log_pow,Real.log_mul (pow_ne_zero _ hr.ne') hs.ne',Real.log_pow] at h1
  have hdiff : Real.log (r/R) ≤ -(19/20)/K := by
    rw [Real.log_div hr.ne' hR.ne']
    calc
      _ = -(Real.log (1+a/K))/2 := by push_cast at h1; linarith only [h1]
      _ ≤ -(19/10/K)/2 := by linarith only [he.trans hlog]
      _ = _ := by ring
  rw [←Real.exp_log (pow_pos (div_pos hr hR) n),Real.log_pow,Real.exp_le_exp]
  have hh := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n)
  exact hh.trans_eq (by ring)

private theorem endpoint_exp : (25:ℝ)*100*48^2 < Real.exp (1563/100) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1563/100) 28
  apply lt_of_lt_of_le _ h
  norm_num [Finset.sum_range_succ,Nat.factorial]

/-- A single monotone bound suffices for all aspects from 48 onward. -/
theorem uniform_fourier_endpoint {x : ℝ} (hx : 48 ≤ x) :
    100*x^2*Real.exp (2997/100-(19/20)*x) < 1/25 := by
  let y := x-48
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hlin : x ≤ 48*Real.exp (y/48) := by
    have hh := Real.add_one_le_exp (y/48)
    dsimp [y] at hh; linarith
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ x) hlin 2
  have h := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (2997/100-(19/20)*x)).le
  have he : (48*Real.exp (y/48))^2*Real.exp (2997/100-(19/20)*x) ≤
      48^2*Real.exp (-(1563/100)) := by
    rw [mul_pow,←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    dsimp only [y]; push_cast; linarith
  have hlast : 100*(48^2*Real.exp (-(1563/100))) < 1/25 := by
    calc
      _ = 100*48^2/Real.exp (1563/100) := by rw [Real.exp_neg]; ring
      _ < _ := (div_lt_div_iff₀ (Real.exp_pos _) (by norm_num)).mpr (by linarith only [endpoint_exp])
  calc
    _ = 100*(x^2*Real.exp (2997/100-(19/20)*x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h.trans he) (by norm_num : (0:ℝ) ≤ 100)
    _ < _ := hlast

/-- The two amplitude ranges give one normalized error target once the lattice
calculus supplies its indicated effective numerator. -/
theorem uniform_normalized_fourier_error {x B C : ℝ} (hx : 48 ≤ x)
    (hC0 : 0 ≤ C) (hC : C ≤ x^2*(110*Real.sqrt x+80))
    (hB₁ : x ≤ 100 → B ≤ 457)
    (hB₂ : 100 ≤ x → B ≤ (46/100)*x*Real.sqrt x) :
    (B*C/(2*x*(x-1)))*Real.exp (2997/100-(19/20)*x) < 1/25 := by
  have hx0 : 0 < x := by linarith
  have hs0 := Real.sqrt_nonneg x
  have hs := Real.sq_sqrt hx0.le
  have hs1 : 13/2 ≤ Real.sqrt x := (sq_le_sq₀ (by norm_num) hs0).mp (by nlinarith only [hs,hx])
  have hB : B ≤ (3/2)*x*Real.sqrt x := by
    rcases le_total x 100 with h | h
    · apply (hB₁ h).trans
      have hh := mul_le_mul hx hs1 (by norm_num : (0:ℝ) ≤ 13/2) hx0.le
      linarith
    · apply (hB₂ h).trans
      nlinarith only [mul_nonneg hx0.le hs0]
  have hC' : C ≤ x^2*(123*Real.sqrt x) :=
    hC.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x))
  have hpos : 0 < 2*x*(x-1) := mul_pos (mul_pos (by norm_num) hx0) (by linarith)
  have hf : B*C/(2*x*(x-1)) ≤ 100*x^2 := by
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ((3/2)*x*Real.sqrt x)*(x^2*(123*Real.sqrt x)) :=
        mul_le_mul hB hC' hC0 (by positivity)
      _ = (369/2)*x^3*(Real.sqrt x)^2 := by ring
      _ = x^3*((369/2)*x) := by rw [hs]; ring
      _ ≤ x^3*(200*(x-1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le).trans_lt (uniform_fourier_endpoint hx)

#print axioms uniform_normalized_fourier_error
#print axioms selected_circle_decay
#print axioms uniform_fourier_endpoint
end OpenMathResearch.LongCycleExcedances
