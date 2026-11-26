import CatalanStrictPeaksRightRootComparison
import CatalanStrictPeaksRightPoleArithmetic
import CatalanStrictPeaksRightPoleCoefficients
import CatalanStrictPeaksPoleValues
import CatalanStrictPeaksRightCheckpoint

open OpenMathResearch.OrientedNegativeInterlace

namespace CatalanStrictPeaks.RightEdge

private theorem rightmost_root_sign_of_pole_bounds {n : ℕ} {K : ℝ} (hK : 1 < K)
    (hv : ∀ m, 150 ≤ m →
      |(C m).eval (-11 / 16) - (11 / 16 : ℝ) * (27 / 16 : ℝ)^m| ≤ 24 * (3 / 2 : ℝ)^m)
    (hd : ∀ m, 150 ≤ m →
      |(C m).derivative.eval (-11 / 16) - K * (9 / 4 : ℝ)^m| ≤ 20 * (m : ℝ) * (27 / 16 : ℝ)^m)
    (hn : 150 ≤ n)
    {old : Fin (rowDegree n) → ℝ} {next : Fin (rowDegree (n+1)) → ℝ}
    (hOld : CompleteNegativeRoots (C n) old) (hNext : CompleteNegativeRoots (C (n+1)) next)
    (i : Fin (rowDegree n)) (hi : i.val = 0) :
    (C (n+1)).eval (-old i) < 0 := by
  have hn' : 150 ≤ n+1 := by omega
  obtain ⟨r, hR, hgap⟩ := CutGeometry.roots_after_first_modulus_gap hn
  obtain ⟨s, hS, hgap'⟩ := CutGeometry.roots_after_first_modulus_gap hn'
  have heq := hR.unique hOld
  have heq' := hS.unique hNext
  rw [heq] at hgap
  rw [heq'] at hgap'
  let v := fun m => (C m).eval (-11 / 16)
  let d := fun m => (C m).derivative.eval (-11 / 16)
  obtain ⟨hval, hlog, hstep⟩ := ratio_growth_of_poles v d hK hv hd hn
  have hval' := (ratio_growth_of_poles v d hK hv hd hn').1
  exact rightmost_sign_of_logDerivative_growth hn hOld hNext hgap hgap' hval hval' hlog hstep i hi

open NearPoleSeries in
/-- At the coalescence parameter the actual row and its derivative obey
the two quantitative pole estimates. -/
theorem row_pole_errors {n : ℕ} (hn : 150 ≤ n) :
    |(C n).eval (-11 / 16) - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n ∧
    |(C n).derivative.eval (-11 / 16) - (16 * Real.sqrt 3 / 27) * (9 / 4 : ℝ) ^ n| ≤
      20 * (n : ℝ) * (27 / 16 : ℝ) ^ n := by
  have hR : ∀ k, |PowerSeries.coeff ℝ k R| ≤ 2 * (5 / 4 : ℝ) ^ k := by
    intro k
    simpa only [Real.norm_eq_abs] using coeff_R_bound k
  have hRi : ∀ k, |PowerSeries.coeff ℝ k Ri| ≤ 3 * (5 / 4 : ℝ) ^ k := by
    intro k
    simpa only [Real.norm_eq_abs] using coeff_Ri_bound k
  have hHa : PoleHasSum (H R) a⁻¹ (11 / 16) := by
    rw [show a⁻¹ = 16 / 27 by norm_num [a]]
    exact hasSum_H_at_a
  have hBb : PoleHasSum (B Ri) b⁻¹ (4 * Real.sqrt 3 / 27) := by
    rw [show b⁻¹ = 4 / 9 by norm_num [b]]
    exact hasSum_B_at_b
  simpa only [tau, a, b] using row_pole_error_of_radical constantCoeff_R R_sq R_mul_Ri
    hR hRi hHa hBb hn

/-- The next row is strictly negative at the rightmost zero of the old row. -/
theorem rightmost_root_sign {n : ℕ} (hn : 150 ≤ n)
    {old : Fin (rowDegree n) → ℝ} {next : Fin (rowDegree (n+1)) → ℝ}
    (hOld : CompleteNegativeRoots (C n) old) (hNext : CompleteNegativeRoots (C (n+1)) next)
    (i : Fin (rowDegree n)) (hi : i.val = 0) :
    (C (n+1)).eval (-old i) < 0 := by
  have hS : (27 / 16 : ℝ) < Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hK : (1 : ℝ) < 16 * Real.sqrt 3 / 27 := by linarith
  exact rightmost_root_sign_of_pole_bounds hK (fun _ h => (row_pole_errors h).1)
    (fun _ h => (row_pole_errors h).2) hn hOld hNext i hi

end CatalanStrictPeaks.RightEdge
