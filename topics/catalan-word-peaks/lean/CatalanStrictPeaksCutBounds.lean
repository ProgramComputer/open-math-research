import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pointwise majorants for the Catalan radial integrand

A square-root factor is specified by its defining equation and nonnegative
real part. The estimates apply to the principal branch along the cuts once
those two properties are supplied.
-/

namespace CatalanStrictPeaks.CutBounds

private theorem factor_norm_sq_le {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) :
    ‖g‖ ^ 2 ≤ 1 + ‖u‖ * s := by
  rw [← norm_pow, h]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖u * (s : ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [norm_mul, Complex.norm_real, abs_of_nonneg hs]

/-- A square-root factor grows at most linearly in the displacement. -/
theorem factor_norm_bound {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) :
    ‖g‖ ≤ 1 + ‖u‖ * s / 2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have H := factor_norm_sq_le hs h
  have hh := sq_nonneg (‖u‖ * s / 2)
  nlinarith

private theorem factor_difference_bound {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) (hr : 0 ≤ g.re) :
    ‖g - 1‖ ≤ ‖u‖ * s := by
  have hfac : (g - 1) * (g + 1) = u * (s : ℂ) := by
    calc
      _ = g ^ 2 - 1 := by ring
      _ = _ := by rw [h]; ring
  have hnorm : ‖g - 1‖ * ‖g + 1‖ = ‖u‖ * s := by
    have hh := congrArg norm hfac
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using hh
  have hreal : 1 ≤ (g + 1).re := by simpa [Complex.add_re] using hr
  have hone : 1 ≤ ‖g + 1‖ := hreal.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  calc
    _ = ‖g - 1‖ * 1 := by rw [mul_one]
    _ ≤ ‖g - 1‖ * ‖g + 1‖ := mul_le_mul_of_nonneg_left hone (norm_nonneg _)
    _ = _ := hnorm

/-- Modulus and loss bounds for two factors whose coefficients have modulus at most one. -/
theorem short_product {s : ℝ} (hs : 0 ≤ s) {u v g h : ℂ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hg : g ^ 2 = 1 + u * (s : ℂ)) (hh : h ^ 2 = 1 + v * (s : ℂ))
    (hgr : 0 ≤ g.re) (hhr : 0 ≤ h.re) :
    ‖g * h‖ ≤ 1 + s ∧ ‖g * h - 1‖ ≤ 2 * s + s ^ 2 / 2 := by
  have hgs : ‖g‖ ^ 2 ≤ 1 + s := (factor_norm_sq_le hs hg).trans
    (by linarith [mul_le_mul_of_nonneg_right hu hs])
  have hhs : ‖h‖ ^ 2 ≤ 1 + s := (factor_norm_sq_le hs hh).trans
    (by linarith [mul_le_mul_of_nonneg_right hv hs])
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_mul, mul_pow, pow_two (1 + s)]
    exact mul_le_mul hgs hhs (sq_nonneg _) (by positivity)
  · have hg₁ : ‖g - 1‖ ≤ s := (factor_difference_bound hs hg hgr).trans
      (by simpa using mul_le_mul_of_nonneg_right hu hs)
    have hh₁ : ‖h - 1‖ ≤ s := (factor_difference_bound hs hh hhr).trans
      (by simpa using mul_le_mul_of_nonneg_right hv hs)
    have hhNorm : ‖h‖ ≤ 1 + s / 2 := (factor_norm_bound hs hh).trans
      (by linarith [mul_le_mul_of_nonneg_right hv hs])
    have hdec : g * h - 1 = (g - 1) * h + (h - 1) := by ring
    calc
      _ ≤ ‖g - 1‖ * ‖h‖ + ‖h - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ s * (1 + s / 2) + s :=
        add_le_add (mul_le_mul hg₁ hhNorm (norm_nonneg _) hs) hh₁
      _ = _ := by ring

/-- The modulus and difference bounds for one long and two bounded factors. -/
theorem three_factor_majorants {s ell : ℝ} (hs : 0 ≤ s) (hell : 0 ≤ ell)
    {u₁ u₂ u₃ g₁ g₂ g₃ : ℂ} (hu₁ : ‖u₁‖ ≤ ell) (hu₂ : ‖u₂‖ ≤ 1) (hu₃ : ‖u₃‖ ≤ 1)
    (hg₁ : g₁ ^ 2 = 1 + u₁ * (s : ℂ)) (hg₂ : g₂ ^ 2 = 1 + u₂ * (s : ℂ))
    (hg₃ : g₃ ^ 2 = 1 + u₃ * (s : ℂ))
    (hr₁ : 0 ≤ g₁.re) (hr₂ : 0 ≤ g₂.re) (hr₃ : 0 ≤ g₃.re) :
    ‖g₁ * (g₂ * g₃)‖ ≤ (1 + s) * (1 + ell * s / 2) ∧
      ‖g₁ * (g₂ * g₃) - 1‖ ≤ (ell + 2) * s + (ell + 1 / 2) * s ^ 2 := by
  obtain ⟨hNorm, hDiff⟩ := short_product hs hu₂ hu₃ hg₂ hg₃ hr₂ hr₃
  have hlong := mul_le_mul_of_nonneg_right hu₁ hs
  constructor
  · rw [norm_mul, mul_comm (1 + s)]
    exact mul_le_mul ((factor_norm_bound hs hg₁).trans (by linarith [hlong]))
      hNorm (norm_nonneg _) (by positivity)
  · have hdec : g₁ * (g₂ * g₃) - 1 = (g₁ - 1) * (g₂ * g₃) + (g₂ * g₃ - 1) :=
      by ring
    calc
      _ ≤ ‖g₁ - 1‖ * ‖g₂ * g₃‖ + ‖g₂ * g₃ - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ (ell * s) * (1 + s) + (2 * s + s ^ 2 / 2) :=
        add_le_add (mul_le_mul ((factor_difference_bound hs hg₁ hr₁).trans hlong)
          hNorm (norm_nonneg _) (mul_nonneg hell hs)) hDiff
      _ = _ := by ring

/-- The reciprocal factors at the near branch point. -/
noncomputable def shortReciprocal (b : ℂ) (s : ℝ) : ℂ :=
  (1 + (s : ℂ))⁻¹ * (1 + b * (s : ℂ))⁻¹

private theorem norm_one_add_lower (u : ℂ) : 1 - ‖u‖ ≤ ‖1 + u‖ := by
  simpa only [norm_one, norm_neg, sub_neg_eq_add] using norm_sub_norm_le (1 : ℂ) (-u)

private theorem reciprocal_majorants {b : ℂ} {s q : ℝ} (hs : 0 ≤ s)
    (hb : ‖b‖ ≤ 3) (hq : 0 < q) (hqs : q ≤ 1 - 3 * s) :
    ‖shortReciprocal b s‖ ≤ 1 / q ∧
      ‖shortReciprocal b s - 1‖ ≤ (3 / q + 1) * s := by
  let u := b * (s : ℂ)
  let v := (s : ℂ)
  have hu : ‖u‖ ≤ 3 * s := by
    simpa only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using
      mul_le_mul_of_nonneg_right hb hs
  have huNorm : q ≤ ‖1 + u‖ := (show q ≤ 1 - ‖u‖ by linarith).trans
    (norm_one_add_lower u)
  have huPos : 0 < ‖1 + u‖ := hq.trans_le huNorm
  have huNe : 1 + u ≠ 0 := norm_pos_iff.mp huPos
  have hvNorm : ‖1 + v‖ = 1 + s := by
    rw [show 1 + v = ((1 + s : ℝ) : ℂ) by simp [v], Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hvPos : 0 < ‖1 + v‖ := hvNorm ▸ (by positivity : 0 < 1 + s)
  have hvNe : 1 + v ≠ 0 := norm_pos_iff.mp hvPos
  have huInv : ‖(1 + u)⁻¹‖ ≤ 1 / q := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ huPos]
    rw [one_div_mul_eq_div]
    exact (one_le_div hq).mpr huNorm
  have hvInv : ‖(1 + v)⁻¹‖ ≤ 1 := by
    rw [norm_inv, hvNorm, inv_eq_one_div, div_le_one (by positivity)]
    linarith
  constructor
  · change ‖(1 + v)⁻¹ * (1 + u)⁻¹‖ ≤ 1 / q
    rw [norm_mul]
    simpa using mul_le_mul hvInv huInv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hInv (z : ℂ) (hz : 1 + z ≠ 0) : (1 + z)⁻¹ - 1 = -z / (1 + z) := by
      field_simp
    have hU : ‖(1 + u)⁻¹ - 1‖ ≤ (3 / q) * s := by
      rw [hInv u huNe, norm_div, norm_neg, div_le_iff₀ huPos]
      calc
        _ ≤ 3 * s := hu
        _ = ((3 / q) * s) * q := by field_simp [hq.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left huNorm (by positivity)
    have hV : ‖(1 + v)⁻¹ - 1‖ ≤ s := by
      rw [hInv v hvNe, norm_div, norm_neg, hvNorm, div_le_iff₀ (by positivity)]
      simp only [v, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      nlinarith
    change ‖(1 + v)⁻¹ * (1 + u)⁻¹ - 1‖ ≤ (3 / q + 1) * s
    have hdec :
        (1 + v)⁻¹ * (1 + u)⁻¹ - 1 =
          (1 + v)⁻¹ * ((1 + u)⁻¹ - 1) + ((1 + v)⁻¹ - 1) := by ring
    calc
      _ ≤ ‖(1 + v)⁻¹‖ * ‖(1 + u)⁻¹ - 1‖ + ‖(1 + v)⁻¹ - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ 1 * ((3 / q) * s) + s :=
        add_le_add (mul_le_mul hvInv hU (norm_nonneg _) (by norm_num)) hV
      _ = _ := by ring

/-- Bounds for the reciprocal up to displacement one eighth. -/
theorem short_reciprocal_bounds {b : ℂ} {s : ℝ} (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8)
    (hb : ‖b‖ ≤ 3) :
    ‖shortReciprocal b s‖ ≤ 8 / 5 ∧ ‖shortReciprocal b s - 1‖ ≤ (29 / 5) * s := by
  have h := reciprocal_majorants hs hb (q := 5 / 8) (by norm_num) (by linarith)
  convert h using 1 <;> norm_num

/-- Bounds for the reciprocal on the longer local interval of the covariance argument. -/
theorem sixth_reciprocal_bounds {b : ℂ} {s : ℝ} (hs : 0 ≤ s) (hs₆ : s ≤ 1 / 6)
    (hb : ‖b‖ ≤ 3) :
    ‖shortReciprocal b s‖ ≤ 2 ∧ ‖shortReciprocal b s - 1‖ ≤ 7 * s := by
  have h := reciprocal_majorants hs hb (q := 1 / 2) (by norm_num) (by linarith)
  convert h using 1 <;> norm_num

/-- Local integrand error before taking the beta expectation. -/
theorem near_local_error {b K : ℂ} {s ell n : ℝ}
    (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8) (hb : ‖b‖ ≤ 3) (hell : ell ≤ n / 4)
    (hK : ‖K - 1‖ ≤ (ell + 2) * s + (ell + 1 / 2) * s ^ 2) :
    ‖shortReciprocal b s * K - 1‖ ≤ (2 * n / 5 + 9) * s +
      (2 * n / 5 + 4 / 5) * s ^ 2 := by
  let R := shortReciprocal b s
  obtain ⟨hRN, hRD⟩ := short_reciprocal_bounds hs hs₈ hb
  have hdec : R * K - 1 = R * (K - 1) + (R - 1) := by ring
  change ‖R * K - 1‖ ≤ _
  calc
    _ ≤ ‖R‖ * ‖K - 1‖ + ‖R - 1‖ := by
      rw [hdec, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ (8 / 5) * ((ell + 2) * s + (ell + 1 / 2) * s ^ 2) + (29 / 5) * s :=
      add_le_add (mul_le_mul hRN hK (norm_nonneg _) (by norm_num)) hRD
    _ = (8 * ell / 5 + 9) * s + (8 * ell / 5 + 4 / 5) * s ^ 2 := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (by linarith) hs)
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end CatalanStrictPeaks.CutBounds
