import NumeratorOddPoleMoment
import NumeratorTaylorContraction

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

/-- Degree-normalized coefficients of the logistic logarithm, expressed by
its linear logistic value and the full odd-pole sum at every higher degree. -/
def numeratorLogSeries (s : ℝ) (j : ℕ) : ℂ :=
  if j = 0 then 0
  else if j = 1 then (numeratorRadius s/(1+Real.exp s):ℝ)
  else -(∑' l : ℤ, ((numeratorRadius s:ℂ)/numeratorPole s l)^j)/(j:ℂ)

private theorem numerator_linear_bound {s : ℝ} (hs : 0 ≤ s) :
    ‖numeratorLogSeries s 1‖ ≤ 4 := by
  have hp := Real.pi_pos
  have hr : numeratorRadius s ≤ s+π := by
    unfold numeratorRadius
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [mul_nonneg hs hp.le]⟩
  unfold numeratorLogSeries
  rw [if_neg one_ne_zero, if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (numeratorRadius_pos s).le (by positivity))]
  apply (div_le_iff₀ (by positivity : 0 < 1+Real.exp s)).2
  have h := Real.add_one_le_exp s
  linarith only [hr,h,Real.pi_lt_four,hs]

private theorem numerator_log_series_envelope (s : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    ‖numeratorLogSeries s j‖ ≤
      (2+9/(4*(π/numeratorRadius s)*Real.sqrt j))/(j:ℝ) := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  let f : ℤ → ℂ := fun l => ((numeratorRadius s:ℂ)/numeratorPole s l)^j
  have hnorm (l : ℤ) : ‖f l‖ = (numeratorRadius s/‖numeratorPole s l‖)^j := by
    simp [f,norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (numeratorRadius_pos s)]
  have hm := numerator_actual_pole_moment s hj
  have hsum : Summable (fun l => ‖f l‖) := by simp_rw [hnorm]; exact hm.1
  have hbound := (norm_tsum_le_tsum_norm hsum).trans (show (∑' l, ‖f l‖) ≤ _ by
    simp_rw [hnorm]
    exact hm.2)
  change ‖(if j=0 then _ else if j=1 then _ else -(∑' l, f l)/(j:ℂ))‖ ≤ _
  rw [if_neg hj0, if_neg hj1,norm_div,norm_neg,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg j)

/-- Exact contraction for the all-degree odd-pole series of the original
logistic numerator. The evaluation points use the normalized radius. -/
theorem numerator_logarithm_series_contraction {s : ℝ} (hs : 0 ≤ s)
    {k : ℕ} (hk : 100 ≤ k) (hsh : s ≤ 4*Real.sqrt k) {R : ℝ}
    (hR : 1 ≤ R) (hRu : R ≤ 1+1/(k:ℝ)) {ξ η : ℂ}
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    let c := numeratorLogSeries s
    let ρ : ℂ := ((1-1/(k:ℝ):ℝ):ℂ)
    ‖numeratorTaylor k c ((R:ℂ)*ξ) - (∑' j, c j * (ρ*ξ)^j)‖ +
      ‖numeratorTaylor k c η - (∑' j, c j * (ρ*η)^j)‖ ≤ (2997:ℝ)/100 := by
  have hS : 0 < π/numeratorRadius s := div_pos Real.pi_pos (numeratorRadius_pos s)
  have hU : 1/((π/numeratorRadius s)*Real.sqrt k) ≤ 32/25 := by
    rw [show 1/((π/numeratorRadius s)*Real.sqrt k) =
      numeratorRadius s/(π*Real.sqrt k) by
        field_simp [Real.pi_ne_zero, (numeratorRadius_pos s).ne',
          show (Real.sqrt (k:ℝ))≠0 from (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < k by omega))).ne']]
    exact numerator_small_height_scale hs hk hsh
  exact numerator_small_height_contraction hk _ hS hU hR hRu hξ hη
    (numerator_linear_bound hs) (fun _ hj => numerator_log_series_envelope s hj)

#print axioms numerator_logarithm_series_contraction
end OpenMathResearch.LongCycleExcedances
