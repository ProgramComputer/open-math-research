import CatalanStrictPeaksAnalyticBranch
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Continuous square roots on closed logarithmic strips

The map `x ↦ exp x` sends the bottom and top of a width-`2π` strip to
the same radial ray. The square root of `1 - exp x / R` takes its two
one-sided values there. The explicit continuous extension supplies the
boundary values for Cauchy–Goursat on sector rectangles.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex Set

private noncomputable def sidedRoot (side : ℝ) (u : ℂ) : ℂ :=
  (Real.sqrt ((‖u‖ + u.re) / 2) : ℂ) +
    ((side * Real.sqrt ((‖u‖ - u.re) / 2) : ℝ) : ℂ) * I

private theorem sidedRoot_continuous (side : ℝ) : Continuous (sidedRoot side) := by
  unfold sidedRoot
  fun_prop

private theorem sidedRoot_real_nonneg (side a : ℝ) (ha : 0 ≤ a) :
    sidedRoot side (a : ℂ) = (Real.sqrt a : ℂ) := by
  have h : (a + a) / 2 = a := by ring
  simp [sidedRoot, abs_of_nonneg ha, h]

private theorem sidedRoot_real_nonpos (side a : ℝ) (ha : a ≤ 0) :
    sidedRoot side (a : ℂ) = ((side * Real.sqrt (-a) : ℝ) : ℂ) * I := by
  have h : (-a - a) / 2 = -a := by ring
  simp [sidedRoot, abs_of_nonpos ha, h]

private theorem sidedRoot_above {u : ℂ} (h : 0 ≤ u.im) :
    sidedRoot 1 u = principalRoot u := by
  apply Complex.ext
  · simp [sidedRoot, principalRoot, Complex.mul_re, cpow_inv_two_re]
  · simp [sidedRoot, principalRoot, Complex.mul_im, cpow_inv_two_im_eq_sqrt h]

private theorem sidedRoot_below {u : ℂ} (h : u.im ≤ 0) (hu : u ∈ slitPlane) :
    sidedRoot (-1) u = principalRoot u := by
  rcases h.lt_or_eq with hneg | hzero
  · apply Complex.ext
    · simp [sidedRoot, principalRoot, Complex.mul_re, cpow_inv_two_re]
    · simp [sidedRoot, principalRoot, Complex.mul_im, cpow_inv_two_im_eq_neg_sqrt hneg]
  · have hEq : (u.re : ℂ) = u := by apply Complex.ext <;> simp [hzero]
    have hRe : 0 < u.re := hu.resolve_right (not_not_intro hzero)
    rw [← hEq, sidedRoot_real_nonneg (-1) _ hRe.le, ← sidedRoot_above]
    · exact (sidedRoot_real_nonneg 1 _ hRe.le).symm
    · simp

private noncomputable def logRootArgument (R : ℝ) (x : ℂ) : ℂ :=
  1 - exp x / (R : ℂ)

/-- Extend the principal square root from inside a full logarithmic strip. -/
noncomputable def logStripRoot (R : ℝ) (x : ℂ) : ℂ :=
  if x.im ≤ Real.pi then sidedRoot (-1) (logRootArgument R x)
  else sidedRoot 1 (logRootArgument R x)

private theorem logRootArgument_im (R : ℝ) (x : ℂ) :
    (logRootArgument R x).im = -(Real.exp x.re * Real.sin x.im / R) := by
  simp [logRootArgument, Complex.exp_im]

private theorem logRootArgument_at {R : ℝ} (x y : ℝ) (hc : Real.cos y = 1)
    (hs : Real.sin y = 0) :
    logRootArgument R ((x : ℂ) + (y : ℂ) * I) = ((1 - Real.exp x / R : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [logRootArgument, Complex.exp_re, Complex.mul_re, Complex.mul_im, hc]
  · simp [logRootArgument_im, Complex.mul_im, hs]

private theorem logRootArgument_pi (R : ℝ) {x : ℂ} (hx : x.im = Real.pi) :
    logRootArgument R x = ((1 + Real.exp x.re / R : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [logRootArgument, Complex.exp_re, hx, sub_neg_eq_add, neg_div]
  · simp [logRootArgument_im, hx]

/-- The changes in the imaginary part of the square root agree at angle π. -/
theorem logStripRoot_continuous {R : ℝ} (hR : 0 < R) : Continuous (logStripRoot R) := by
  have hArg : Continuous (logRootArgument R) := by
    unfold logRootArgument
    fun_prop
  unfold logStripRoot
  apply Continuous.if_le ((sidedRoot_continuous (-1)).comp hArg)
    ((sidedRoot_continuous 1).comp hArg) continuous_im continuous_const
  intro x hx
  simp only [Function.comp_apply]
  rw [logRootArgument_pi R hx, sidedRoot_real_nonneg, sidedRoot_real_nonneg]
  all_goals positivity

private theorem sin_neg_between_pi_two_pi {y : ℝ}
    (h₁ : Real.pi < y) (h₂ : y < 2 * Real.pi) : Real.sin y < 0 := by
  have hSin := Real.sin_pos_of_pos_of_lt_pi (show 0 < y - Real.pi by linarith)
    (show y - Real.pi < Real.pi by linarith)
  rw [Real.sin_sub_pi] at hSin
  linarith

theorem exp_div_mem_slitPlane {R : ℝ} (hR : 0 < R) {x : ℂ}
    (h₁ : 0 < x.im) (h₂ : x.im < 2 * Real.pi) :
    1 - exp x / (R : ℂ) ∈ slitPlane := by
  change logRootArgument R x ∈ slitPlane
  rcases lt_trichotomy x.im Real.pi with ha | ha | ha
  · right
    rw [logRootArgument_im]
    exact neg_ne_zero.mpr (div_pos
      (mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h₁ ha)) hR).ne'
  · rw [logRootArgument_pi R ha, ofReal_mem_slitPlane]
    positivity
  · right
    rw [logRootArgument_im]
    exact neg_ne_zero.mpr (div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (Real.exp_pos _) (sin_neg_between_pi_two_pi ha h₂)) hR).ne

/-- Inside the open strip the extension agrees with the principal root. -/
theorem logStripRoot_eq_principal {R : ℝ} (hR : 0 < R) {x : ℂ}
    (h₁ : 0 < x.im) (h₂ : x.im < 2 * Real.pi) :
    logStripRoot R x = principalRoot (1 - exp x / (R : ℂ)) := by
  unfold logStripRoot
  split_ifs with h
  · apply sidedRoot_below _ (exp_div_mem_slitPlane hR h₁ h₂)
    change (logRootArgument R x).im ≤ 0
    rw [logRootArgument_im, neg_nonpos]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi h₁.le h)) hR.le
  · apply sidedRoot_above
    change 0 ≤ (logRootArgument R x).im
    rw [logRootArgument_im, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sin_neg_between_pi_two_pi (lt_of_not_ge h) h₂).le) hR.le

private theorem logRootArgument_real (R x : ℝ) :
    logRootArgument R (x : ℂ) = ((1 - Real.exp x / R : ℝ) : ℂ) := by
  simpa using (logRootArgument_at (R := R) x 0 Real.cos_zero Real.sin_zero)

private theorem logStripRoot_lower_boundary (R x : ℝ) :
    logStripRoot R (x : ℂ) = sidedRoot (-1) ((1 - Real.exp x / R : ℝ) : ℂ) := by
  rw [logStripRoot, if_pos (by simpa using Real.pi_pos.le), logRootArgument_real]

private theorem logStripRoot_upper_boundary (R x : ℝ) :
    logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) =
      sidedRoot 1 ((1 - Real.exp x / R : ℝ) : ℂ) := by
  rw [logStripRoot, if_neg, logRootArgument_at x _ Real.cos_two_pi Real.sin_two_pi]
  simp [Complex.mul_im, not_le, Real.pi_pos]

/-- The two boundary values agree on the inward segment. -/
theorem logStripRoot_boundary_eq (R x : ℝ) (h : Real.exp x / R ≤ 1) :
    logStripRoot R (x : ℂ) = logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) := by
  rw [logStripRoot_lower_boundary, logStripRoot_upper_boundary,
    sidedRoot_real_nonneg _ _ (sub_nonneg.mpr h), sidedRoot_real_nonneg _ _ (sub_nonneg.mpr h)]

/-- The lower-angle boundary value minus the upper-angle one on the outward ray. -/
theorem logStripRoot_jump (R x : ℝ) (h : 1 ≤ Real.exp x / R) :
    logStripRoot R (x : ℂ) - logStripRoot R ((x : ℂ) + (2 * Real.pi : ℝ) * I) =
      -2 * I * (Real.sqrt (Real.exp x / R - 1) : ℂ) := by
  rw [logStripRoot_lower_boundary, logStripRoot_upper_boundary,
    sidedRoot_real_nonpos _ _ (sub_nonpos.mpr h), sidedRoot_real_nonpos _ _ (sub_nonpos.mpr h),
    neg_sub]
  push_cast
  ring

private theorem sidedRoot_sq_real (side a : ℝ) (hside : side ^ 2 = 1) :
    sidedRoot side (a : ℂ) ^ 2 = (a : ℂ) := by
  by_cases h : 0 ≤ a
  · rw [sidedRoot_real_nonneg _ _ h, ← Complex.ofReal_pow, Real.sq_sqrt h]
  · have ha := (lt_of_not_ge h).le
    rw [sidedRoot_real_nonpos _ _ ha, mul_pow, ← Complex.ofReal_pow, mul_pow, hside, one_mul,
      Real.sq_sqrt (neg_nonneg.mpr ha), I_sq, Complex.ofReal_neg]
    ring

/-- The defining square holds up to and including both edges of the strip. -/
theorem logStripRoot_sq {R : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : 0 ≤ z.im) (h₂ : z.im ≤ 2 * Real.pi) :
    logStripRoot R z ^ 2 = 1 - exp z / (R : ℂ) := by
  change logStripRoot R z ^ 2 = logRootArgument R z
  rcases h₁.eq_or_lt with hbot | hlo
  · have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [← hbot]
    rw [hz, logStripRoot_lower_boundary, logRootArgument_real, sidedRoot_sq_real]
    norm_num
  rcases h₂.eq_or_lt with htop | hhi
  · have hz : z = (z.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [htop, Complex.mul_re, Complex.mul_im]
    rw [hz, logStripRoot_upper_boundary, logRootArgument_at _ _ Real.cos_two_pi Real.sin_two_pi,
      sidedRoot_sq_real]
    norm_num
  rw [logStripRoot_eq_principal hR hlo hhi, principalRoot_sq]
  rfl

private theorem principalRoot_real_nonneg {a : ℝ} (ha : 0 ≤ a) :
    principalRoot (a : ℂ) = (Real.sqrt a : ℂ) := by
  rw [← sidedRoot_above (u := (a : ℂ)) (by simp), sidedRoot_real_nonneg _ _ ha]

/-- On circles inside the branch point, the same principal root also gives
both boundary values of the logarithmic strip. -/
theorem logStripRoot_eq_principal_of_le_radius {R : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : 0 ≤ z.im) (h₂ : z.im ≤ 2 * Real.pi) (hRz : ‖exp z‖ ≤ R) :
    logStripRoot R z = principalRoot (1 - exp z / (R : ℂ)) := by
  have h₃ : 0 ≤ 1 - Real.exp z.re / R := sub_nonneg.mpr
    ((div_le_one hR).mpr (by simpa only [norm_exp] using hRz))
  change logStripRoot R z = principalRoot (logRootArgument R z)
  rcases h₁.eq_or_lt with hbot | hlo
  · have hz : z = (z.re : ℂ) := by apply Complex.ext <;> simp [← hbot]
    rw [hz, logStripRoot_lower_boundary, logRootArgument_real,
      sidedRoot_real_nonneg _ _ h₃, principalRoot_real_nonneg h₃]
  rcases h₂.eq_or_lt with htop | hhi
  · have hz : z = (z.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [htop, Complex.mul_re, Complex.mul_im]
    rw [hz, logStripRoot_upper_boundary, logRootArgument_at _ _ Real.cos_two_pi Real.sin_two_pi,
      sidedRoot_real_nonneg _ _ h₃, principalRoot_real_nonneg h₃]
  exact logStripRoot_eq_principal hR hlo hhi

private theorem logRootArgument_shift (R θ : ℝ) (z : ℂ) :
    logRootArgument R (z - (θ : ℂ) * I) =
      1 - exp z / ((R : ℂ) * exp ((θ : ℂ) * I)) := by
  rw [logRootArgument, Complex.exp_sub, div_div, mul_comm (exp _)]

/-- Rotating the open strip avoids the radial cut of the rotated factor. -/
theorem exp_div_mem_slitPlane_shift {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ < z.im) (h₂ : z.im < θ + 2 * Real.pi) :
    1 - exp z / ((R : ℂ) * exp ((θ : ℂ) * I)) ∈ slitPlane := by
  rw [← logRootArgument_shift]
  apply exp_div_mem_slitPlane hR
  · simp [Complex.mul_im]; linarith
  · simp [Complex.mul_im]; linarith

/-- Rotating the strip handles the radial cut in the direction of a branch point. -/
theorem logStripRoot_eq_cutFactor {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ < z.im) (h₂ : z.im < θ + 2 * Real.pi) :
    logStripRoot R (z - (θ : ℂ) * I) = cutFactor ((R : ℂ) * exp ((θ : ℂ) * I)) (exp z) := by
  rw [logStripRoot_eq_principal hR, cutFactor, Complex.exp_sub, div_div, mul_comm (exp _)]
  · simp [Complex.mul_im]
    linarith
  · simp [Complex.mul_im]
    linarith

/-- The rotated strip branch agrees with the principal factor up to both
edges on a circle inside its branch point. -/
theorem logStripRoot_eq_cutFactor_of_le_radius {R θ : ℝ} (hR : 0 < R) {z : ℂ}
    (h₁ : θ ≤ z.im) (h₂ : z.im ≤ θ + 2 * Real.pi) (hz : ‖exp z‖ ≤ R) :
    logStripRoot R (z - (θ : ℂ) * I) = cutFactor ((R : ℂ) * exp ((θ : ℂ) * I)) (exp z) := by
  rw [logStripRoot_eq_principal_of_le_radius hR]
  · change principalRoot (logRootArgument R (z - (θ : ℂ) * I)) = _
    rw [logRootArgument_shift, cutFactor]
  · simp [Complex.mul_im]; linarith
  · simp [Complex.mul_im]; linarith
  · simpa [norm_exp, Complex.mul_re] using hz

end CatalanStrictPeaks.CutGeometry
