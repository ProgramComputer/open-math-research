import SmallCutoffAmplitude

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- A uniform bound on the trace and decay of the selected radius give both
coefficient estimates without integration by parts at finite cutoffs. -/
theorem small_cutoff_cauchy_pair {n : ℕ} {k M r R U C S : ℝ}
    (hn : 10000≤(n:ℝ)) (hk : 0<k) (hr : 0<r) (hR : r≤R) (hU : 0<U)
    (hC : |C|≤1) (hS : 0≤S) (hm : 1≤(n:ℝ)*S^2)
    (hcases : (k≤100 ∧ M≤32) ∨ (k≤50 ∧ M≤60) ∨ (k≤10 ∧ M≤100))
    (hdec : (r/R)^n ≤ exp (-(4/5)*((n:ℝ)/k))) (f : ℝ → ℂ)
    (hf : ∀ y, r*‖f y‖/U ≤ 2*(n:ℝ)^2*exp M) :
    let F := normalizedFourierIntegral f
    let W := r/(2*U)*(r/R)^n
    W*‖F n‖ < 1/25 ∧ W*‖((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(C:ℂ)*F n‖ < S/25 := by
  intro F W
  have hn0 : (0:ℝ)<n := by linarith
  have hR0 := hr.trans_le hR
  let B := 2*(n:ℝ)^2*exp M*U/r
  have hb : 0≤B := by dsimp only [B]; positivity
  have hF (j : ℤ) : ‖F j‖ ≤ B := normalized_coefficient_le_sup (fun y =>
    (le_div_iff₀ hr).mpr (by linarith only [(div_le_iff₀ hU).mp (hf y)])) j
  have hW : 0≤W := by dsimp only [W]; positivity
  have hW_eq : W*B=(n:ℝ)^2*exp M*(r/R)^n := by
    dsimp only [W,B]; field_simp; ring
  let E := 1300*(n:ℝ)^2*exp (M-(4/5)*((n:ℝ)/k))
  have hWE : W*B ≤ E := by
    rw [hW_eq]
    calc
      _ ≤ (n:ℝ)^2*exp M * exp (-(4/5)*((n:ℝ)/k)) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = (n:ℝ)^2*exp (M-(4/5)*((n:ℝ)/k)) := by rw [mul_assoc,←exp_add]; ring_nf
      _ ≤ E := by dsimp only [E]; nlinarith only [mul_nonneg (sq_nonneg (n:ℝ)) (exp_pos (M-(4/5)*((n:ℝ)/k))).le]
  have he₀ : E<1/(100*(n:ℝ)) := small_cutoff_cauchy_decay hn hk hcases
  have he₁ : E<S/100 := small_cutoff_cauchy_sine_error hn hk hcases hS hm
  have hratio : ‖(r:ℂ)/(R:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hr,abs_of_pos hR0]
    exact (div_le_one hR0).mpr hR
  have hcoeff : ‖((r:ℂ)/(R:ℂ))*F ((n:ℤ)+1)-(C:ℂ)*F n‖ ≤ 2*B := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hp := mul_le_mul hratio (hF ((n:ℤ)+1)) (norm_nonneg _) zero_le_one
    have ho := mul_le_mul hC (hF n) (norm_nonneg _) zero_le_one
    linarith
  constructor
  · apply (mul_le_mul_of_nonneg_left (hF n) hW).trans_lt
    apply (hWE.trans_lt he₀).trans_le
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hn])
  · have h := mul_le_mul_of_nonneg_left hcoeff hW
    linarith only [h,hWE,he₁,hS,show W*(2*B)=2*(W*B) by ring]

#print axioms small_cutoff_cauchy_pair
end OpenMathResearch.LongCycleExcedances
