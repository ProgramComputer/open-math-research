import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Cauchy deformation through a finite chain of logarithmic sectors

Under the exponential map, horizontal sides of a rectangle become
radial segments and vertical sides become circular arcs. The two
one-sided functions at each angle may have different values. Summing
Cauchy–Goursat on the rectangles gives the integral of these jumps.
-/

namespace OpenMathResearch.LogarithmicContour

open Complex Set MeasureTheory
open scoped Interval

/-- The coefficient contour in logarithmic coordinates. -/
theorem circleIntegral_eq_angular (f : ℂ → ℂ) (a : ℝ) (n : ℕ) :
    (∮ z in C(0, Real.exp a), (z⁻¹) ^ (n + 1) * f z) =
      I • (∫ y : ℝ in (0)..2 * Real.pi,
        (exp ((a : ℂ) + (y : ℂ) * I))⁻¹ ^ n * f (exp ((a : ℂ) + (y : ℂ) * I))) := by
  rw [circleIntegral, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro y _
  let z := exp ((a : ℂ) + (y : ℂ) * I)
  have hz : z ≠ 0 := exp_ne_zero _
  have hy : circleMap 0 (Real.exp a) y = z := by simp [z, circleMap, exp_add, ofReal_exp]
  change deriv (circleMap 0 (Real.exp a)) y •
    ((circleMap 0 (Real.exp a) y)⁻¹ ^ (n + 1) * f (circleMap 0 (Real.exp a) y)) =
      I • (z⁻¹ ^ n * f z)
  rw [deriv_circleMap, hy]
  change (z * I) * (z⁻¹ ^ (n + 1) * f z) = I * (z⁻¹ ^ n * f z)
  rw [pow_succ]
  calc
    _ = (z * z⁻¹) * (I * (z⁻¹ ^ n * f z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz, one_mul]

private noncomputable def sideIntegral (f : ℂ → ℂ) (a b θ : ℝ) : ℂ :=
  ∫ x in a..b, f ((x : ℂ) + (θ : ℂ) * I)

private noncomputable def arcIntegral (f : ℂ → ℂ) (a θ φ : ℝ) : ℂ :=
  I • ∫ y in θ..φ, f ((a : ℂ) + (y : ℂ) * I)

private theorem rectangle {f : ℂ → ℂ} {a b θ φ : ℝ} (hab : a ≤ b) (hθφ : θ ≤ φ)
    (hc : ContinuousOn f (Icc a b ×ℂ Icc θ φ))
    (hd : DifferentiableOn ℂ f (Ioo a b ×ℂ Ioo θ φ)) :
    arcIntegral f a θ φ = arcIntegral f b θ φ +
      (sideIntegral f a b θ - sideIntegral f a b φ) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ⟨a, θ⟩ ⟨b, φ⟩
    (by simpa [uIcc_of_le hab, uIcc_of_le hθφ] using hc)
    (by simpa [min_eq_left hab, max_eq_right hab, min_eq_left hθφ, max_eq_right hθφ] using hd)
  change sideIntegral f a b θ - sideIntegral f a b φ +
    arcIntegral f b θ φ - arcIntegral f a θ φ = 0 at h
  linear_combination -h

/-- Deform the inner angular integral to the outer arcs and the inward-to-outward
integrals of the jumps encountered at the intervening angles. -/
theorem deform {m : ℕ} {a b : ℝ} (hab : a ≤ b)
    (angle : ℕ → ℝ) (hAngle : Monotone angle)
    (sector : ℕ → ℂ → ℂ) (inner : ℝ → ℂ)
    (hc : ∀ j ≤ m, ContinuousOn (sector j)
      (Icc a b ×ℂ Icc (angle j) (angle (j + 1))))
    (hd : ∀ j ≤ m, DifferentiableOn ℂ (sector j)
      (Ioo a b ×ℂ Ioo (angle j) (angle (j + 1))))
    (hInner : ∀ j ≤ m, ∀ y ∈ Icc (angle j) (angle (j + 1)),
      sector j ((a : ℂ) + (y : ℂ) * I) = inner y)
    (hIntegrable : ∀ j ≤ m, IntervalIntegrable inner volume (angle j) (angle (j + 1)))
    (hPeriod : ∀ x ∈ Icc a b,
      sector 0 ((x : ℂ) + (angle 0 : ℂ) * I) =
        sector m ((x : ℂ) + (angle (m + 1) : ℂ) * I)) :
    I • (∫ y in (angle 0)..angle (m + 1), inner y) =
      (∑ j ∈ Finset.range (m + 1),
        I • (∫ y in angle j..angle (j + 1), sector j ((b : ℂ) + (y : ℂ) * I))) +
      ∑ j ∈ Finset.range m, (
        ∫ x in a..b, sector (j + 1) ((x : ℂ) + (angle (j + 1) : ℂ) * I) -
          sector j ((x : ℂ) + (angle (j + 1) : ℂ) * I)) := by
  let bottom (j : ℕ) := sideIntegral (sector j) a b (angle j)
  let top (j : ℕ) := sideIntegral (sector j) a b (angle (j + 1))
  have hPeriod' : bottom 0 = top m := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hPeriod x hx
  have hAdj : ∀ j, angle j ≤ angle (j + 1) := fun j => hAngle (Nat.le_succ j)
  have hSideInt (j : ℕ) (hj : j ≤ m) (y : ℝ) (hy : y ∈ Icc (angle j) (angle (j + 1))) :
      IntervalIntegrable (fun x : ℝ => sector j ((x : ℂ) + (y : ℂ) * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply (hc j hj).comp (by fun_prop)
    intro x hx
    simpa only [mem_reProdIm, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add] using And.intro hx hy
  have hArc (j : ℕ) (hj : j < m + 1) :
      I • (∫ y in angle j..angle (j + 1), inner y) =
        arcIntegral (sector j) b (angle j) (angle (j + 1)) + (bottom j - top j) := by
    have hEq : arcIntegral (sector j) a (angle j) (angle (j + 1)) =
        I • (∫ y in angle j..angle (j + 1), inner y) :=
      congrArg (fun x : ℂ => I • x) <| intervalIntegral.integral_congr <|
        fun y hy => hInner j (Nat.le_of_lt_succ hj) y (uIcc_of_le (hAdj j) ▸ hy)
    rw [← hEq]
    exact rectangle hab (hAdj j) (hc j (Nat.le_of_lt_succ hj)) (hd j (Nat.le_of_lt_succ hj))
  have hJumps :
      (∑ j ∈ Finset.range (m + 1), (bottom j - top j)) =
        ∑ j ∈ Finset.range m, (∫ x in a..b,
          sector (j + 1) ((x : ℂ) + (angle (j + 1) : ℂ) * I) -
            sector j ((x : ℂ) + (angle (j + 1) : ℂ) * I)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ' bottom, Finset.sum_range_succ top,
      hPeriod', add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    symm
    exact intervalIntegral.integral_sub
      (hSideInt (j + 1) (Nat.succ_le_of_lt hj') _ ⟨le_rfl, hAdj _⟩)
      (hSideInt j hj'.le _ ⟨hAdj _, le_rfl⟩)
  calc
    _ = ∑ j ∈ Finset.range (m + 1), I • (∫ y in angle j..angle (j + 1), inner y) := by
      rw [← intervalIntegral.sum_integral_adjacent_intervals
        (fun j hj => hIntegrable j (Nat.le_of_lt_succ hj)), Finset.smul_sum]
    _ = ∑ j ∈ Finset.range (m + 1),
        (arcIntegral (sector j) b (angle j) (angle (j + 1)) + (bottom j - top j)) :=
      Finset.sum_congr rfl fun j hj => hArc j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [Finset.sum_add_distrib, hJumps]
      rfl

/-- Change variables from logarithmic radius to normalized outward displacement. -/
theorem integral_logRadius_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {g : ℝ → E} (hg : Continuous g) (a b : ℝ) :
    (∫ x in a..b, g x) =
      ∫ s in (Real.exp a / R - 1)..(Real.exp b / R - 1),
        (1 + s)⁻¹ • g (Real.log (R * (1 + s))) := by
  let r : ℝ → ℝ := fun x => Real.exp x / R - 1
  let dr : ℝ → ℝ := fun x => Real.exp x / R
  let transport : ℝ → E := fun s => (1 + s)⁻¹ • g (Real.log (R * (1 + s)))
  have hUnit (x : ℝ) : 1 + r x = dr x := by dsimp [r, dr]; ring
  have hdrPos (x : ℝ) : 0 < dr x := div_pos (Real.exp_pos _) hR
  have hLog (x : ℝ) : Real.log (R * (1 + r x)) = x := by
    rw [hUnit]
    have hProduct : R * dr x = Real.exp x := by
      dsimp [dr]
      field_simp [hR.ne'] <;> ring
    rw [hProduct, Real.log_exp]
  have hDeriv : ∀ x ∈ uIcc a b, HasDerivAt r (dr x) x := by
    intro x _
    exact ((Real.hasDerivAt_exp x).div_const R).sub_const 1
  have hDr : ContinuousOn dr (uIcc a b) := by
    dsimp [dr]
    fun_prop
  have ht : ContinuousOn transport (r '' uIcc a b) := by
    rintro s ⟨x, _, rfl⟩
    have hOne : (1 + r x) ≠ 0 := by rw [hUnit]; exact (hdrPos x).ne'
    have hContinuousOne : ContinuousAt (fun s : ℝ => 1 + s) (r x) := by fun_prop
    have hContinuousScale : ContinuousAt (fun s : ℝ => R * (1 + s)) (r x) :=
      continuousAt_const.mul hContinuousOne
    have hContinuousLog := hContinuousScale.log (mul_ne_zero hR.ne' hOne)
    exact ((hContinuousOne.inv₀ hOne).smul (hg.continuousAt.comp hContinuousLog)).continuousWithinAt
  have hChange := intervalIntegral.integral_comp_smul_deriv' (g := transport) hDeriv hDr ht
  calc
    _ = ∫ x in a..b, dr x • (transport ∘ r) x := by
      apply intervalIntegral.integral_congr
      intro x _
      change g x = dr x • ((1 + r x)⁻¹ • g (Real.log (R * (1 + r x))))
      rw [hLog, hUnit, smul_smul, mul_inv_cancel₀ (hdrPos x).ne', one_smul]
    _ = _ := hChange

end OpenMathResearch.LogarithmicContour
