import NumeratorLogSeries
import FourierOriginalLog

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open scoped BigOperators Real

/-- Normalize each coefficient of the repository's literal cutoff logarithm
by the nearest-pole radius. Every index below the cutoff agrees with the
corresponding all-degree odd-pole coefficient. -/
theorem numerator_log_coeff_eq_original {s : ℝ} (hs : 0 ≤ s) {k j : ℕ} (hjk : j < k) :
    numeratorLogSeries s j = (numeratorRadius s:ℂ)^j *
      (RepositoryQuotientAudit.cutoffLogCoefficient k (-Real.exp (-s)) j : ℂ) := by
  by_cases hzero : j=0
  · subst j
    simp [numeratorLogSeries,RepositoryQuotientAudit.cutoffLogCoefficient]
  by_cases hone : j=1
  · subst j
    unfold numeratorLogSeries
    rw [if_neg one_ne_zero, if_pos rfl, pow_one, original_cutoff_log_linear,
      Complex.exp_neg, ← Complex.ofReal_exp, ← Complex.ofReal_inv,
      ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    have hEpos := Real.exp_pos s
    have hE : Real.exp s ≠ 0 := hEpos.ne'
    have hEp : 1 + Real.exp s ≠ 0 := (by positivity : 0 < 1+Real.exp s).ne'
    have hEi : 1 + (Real.exp s)⁻¹ ≠ 0 := (by positivity : 0 < 1+(Real.exp s)⁻¹).ne'
    field_simp [hE,hEp,hEi]
    exact Or.inl (add_comm _ _)
  · have hj : 2 ≤ j := by omega
    have hj0 : (j:ℂ) ≠ 0 := by exact_mod_cast hzero
    let f : ℤ → ℂ := fun l => 1/numeratorPole s l^j
    have h := original_cutoff_log_poles hj hjk hs
    change (j:ℂ)*(RepositoryQuotientAudit.cutoffLogCoefficient k (-Real.exp (-s)) j:ℂ) =
      -(∑' l, f l) at h
    unfold numeratorLogSeries
    rw [if_neg hzero,if_neg hone]
    have heq :
        (∑' l : ℤ, ((numeratorRadius s:ℂ)/numeratorPole s l)^j) =
          (numeratorRadius s:ℂ)^j * ∑' l, f l := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      simp [f,div_pow,div_eq_mul_inv,mul_pow]
    rw [heq,← mul_neg,← h]
    field_simp [hj0]
    ring

/-- The finite polynomial in normalized coordinates is the literal cutoff
logarithm evaluated after multiplying the coordinate by the principal radius. -/
theorem numerator_taylor_eq_original {s : ℝ} (hs : 0 ≤ s) (k : ℕ) (z : ℂ) :
    numeratorTaylor k (numeratorLogSeries s) z =
      ∑ j ∈ Finset.range k, (RepositoryQuotientAudit.cutoffLogCoefficient k
        (-Real.exp (-s)) j:ℂ) * ((numeratorRadius s:ℂ)*z)^j := by
  unfold numeratorTaylor
  apply Finset.sum_congr rfl
  intro j hj
  rw [numerator_log_coeff_eq_original hs (Finset.mem_range.mp hj), mul_pow]
  ac_rfl

/-- The small-height estimate for the original cutoff polynomial at both
sample points, compared with the all-degree series at their contractions. -/
theorem numerator_original_cutoff_series_contraction {s : ℝ} (hs : 0 ≤ s)
    {k : ℕ} (hk : 100 ≤ k) (hsh : s ≤ 4*Real.sqrt k) {R : ℝ}
    (hR : 1 ≤ R) (hRu : R ≤ 1+1/(k:ℝ)) {ξ η : ℂ}
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    let G : ℂ → ℂ := fun z =>
      ∑ j ∈ Finset.range k, (RepositoryQuotientAudit.cutoffLogCoefficient k
        (-Real.exp (-s)) j:ℂ) * ((numeratorRadius s:ℂ)*z)^j
    let c := numeratorLogSeries s
    let ρ : ℂ := ((1-1/(k:ℝ):ℝ):ℂ)
    ‖G ((R:ℂ)*ξ) - (∑' j, c j * (ρ*ξ)^j)‖ +
      ‖G η - (∑' j, c j * (ρ*η)^j)‖ ≤ (2997:ℝ)/100 := by
  have h := numerator_logarithm_series_contraction hs hk hsh hR hRu hξ hη
  dsimp only at h ⊢
  simpa only [numerator_taylor_eq_original hs] using h

#print axioms numerator_original_cutoff_series_contraction
#print axioms numerator_log_coeff_eq_original
#print axioms numerator_taylor_eq_original
end OpenMathResearch.LongCycleExcedances
