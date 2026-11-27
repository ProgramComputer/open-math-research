import BalancedOccupiedPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace BalancedEventual.OccupiedPhase

open scoped BigOperators
open Finset

noncomputable section

def mass (d r : ℕ) (v : ℝ) : ℝ :=
  ∑ s ∈ range (r + 1), rowWeight d s * v ^ s

def probability (d r : ℕ) (v : ℝ) (s : ℕ) : ℝ :=
  rowWeight d s * v ^ s / mass d r v

def mean (d r : ℕ) (v : ℝ) : ℝ :=
  ∑ s ∈ range (r + 1), probability d r v s * s

def variance (d r : ℕ) (v : ℝ) : ℝ :=
  ∑ s ∈ range (r + 1), probability d r v s * ((s : ℝ) - mean d r v) ^ 2

theorem mass_pos (d r : ℕ) {v : ℝ} (hv : 0 < v) : 0 < mass d r v := by
  unfold mass
  apply Finset.sum_pos' (fun s _ => by unfold rowWeight; positivity)
  exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp [rowWeight]⟩

theorem probability_nonneg (d r s : ℕ) {v : ℝ} (hv : 0 < v) :
    0 ≤ probability d r v s := by
  unfold probability rowWeight
  exact div_nonneg (by positivity) (mass_pos d r hv).le

theorem sum_probability (d r : ℕ) {v : ℝ} (hv : 0 < v) :
    ∑ s ∈ range (r + 1), probability d r v s = 1 := by
  simp only [probability, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (mass_pos d r hv).ne'

theorem mean_nonneg (d r : ℕ) {v : ℝ} (hv : 0 < v) : 0 ≤ mean d r v :=
  Finset.sum_nonneg fun s _ => mul_nonneg (probability_nonneg d r s hv) (Nat.cast_nonneg _)

theorem mean_le (d r : ℕ) {v : ℝ} (hv : 0 < v) : mean d r v ≤ r := by
  calc
    mean d r v ≤ ∑ s ∈ range (r + 1), probability d r v s * (r : ℝ) :=
      Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hs))
        (probability_nonneg d r s hv)
    _ = r := by rw [← Finset.sum_mul, sum_probability d r hv, one_mul]

private def cis (t : ℝ) : ℂ := Complex.exp (Complex.ofReal t * Complex.I)

private theorem cis_re (t : ℝ) : (cis t).re = Real.cos t := by
  rw [cis, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem cis_im (t : ℝ) : (cis t).im = Real.sin t := by
  rw [cis, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]

private theorem cis_add (a b : ℝ) : cis (a + b) = cis a * cis b := by
  simp only [cis, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem abs_sin_sub_le_two_mul_sq (x : ℝ) : |Real.sin x - x| ≤ 2 * x ^ 2 := by
  by_cases hx : |x| ≤ 1
  · have hn : ‖Complex.ofReal x * Complex.I‖ ≤ 1 := by simpa [norm_mul, Real.norm_eq_abs] using hx
    have hb := (Complex.abs_im_le_norm (cis x - 1 - Complex.ofReal x * Complex.I)).trans
      (Complex.norm_exp_sub_one_sub_id_le hn)
    have hstep : |Real.sin x - x| ≤ x ^ 2 := by
      simpa [cis_im, Complex.sub_im, Complex.mul_im, norm_mul, Real.norm_eq_abs]
        using hb
    linarith [sq_nonneg x]
  · have hx' : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    calc
      |Real.sin x - x| ≤ |Real.sin x| + |x| := by
        simpa using abs_sub_le (Real.sin x) 0 x
      _ ≤ 1 + |x| := add_le_add_right (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) _
      _ ≤ 2 * x ^ 2 := by
        nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr hx') (abs_nonneg x)]

private def centered (d r : ℕ) (v : ℝ) : ℂ :=
  ∑ s ∈ range (r + 1), (probability d r v s : ℂ) *
    cis (((s : ℝ) - mean d r v) * angle d)

private theorem centered_re_bound (d r : ℕ) {v : ℝ} (hv : 0 < v) :
    1 - variance d r v * angle d ^ 2 / 2 ≤ (centered d r v).re := by
  simp only [centered, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, cis_re]
  calc
    1 - variance d r v * angle d ^ 2 / 2 =
      ∑ s ∈ range (r + 1), probability d r v s *
        (1 - (((s : ℝ) - mean d r v) * angle d) ^ 2 / 2) := by
          simp only [mul_sub, mul_one, mul_pow, Finset.sum_sub_distrib, sum_probability d r hv]
          congr 1
          unfold variance
          simp only [div_eq_mul_inv, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ ≤ _ := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos (probability_nonneg d r s hv)

private theorem centered_im_bound (d r : ℕ) {v : ℝ} (hv : 0 < v) :
    |(centered d r v).im| ≤ 2 * (variance d r v * angle d ^ 2) := by
  have hz : ∑ s ∈ range (r + 1), probability d r v s *
      (((s : ℝ) - mean d r v) * angle d) = 0 := by
    simp only [← mul_assoc, ← Finset.sum_mul, mul_sub, Finset.sum_sub_distrib,
      sum_probability d r hv, one_mul]
    change (mean d r v - mean d r v) * angle d = 0
    simp
  simp only [centered, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, cis_im]
  rw [← sub_zero (∑ s ∈ range (r + 1), probability d r v s *
    Real.sin (((s : ℝ) - mean d r v) * angle d)), ← hz, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ range (r + 1), |probability d r v s *
        (Real.sin (((s : ℝ) - mean d r v) * angle d) -
          (((s : ℝ) - mean d r v) * angle d))| := by
      simpa only [mul_sub] using Finset.abs_sum_le_sum_abs
        (fun s => probability d r v s * (Real.sin (((s : ℝ) - mean d r v) * angle d) -
          (((s : ℝ) - mean d r v) * angle d))) (range (r + 1))
    _ ≤ ∑ s ∈ range (r + 1), probability d r v s *
        (2 * (((s : ℝ) - mean d r v) * angle d) ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_nonneg (probability_nonneg d r s hv)]
      exact mul_le_mul_of_nonneg_left (abs_sin_sub_le_two_mul_sq _) (probability_nonneg d r s hv)
    _ = _ := by
      unfold variance
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

private theorem arg_abs_le_pi_mul_im {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    |z.arg| ≤ Real.pi * |z.im| := by
  have hnorm : 1 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hnorm' : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hnorm
  have hs := Real.mul_abs_le_abs_sin (Complex.abs_arg_le_pi_div_two_iff.mpr
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hz))
  rw [Complex.sin_arg, abs_div, abs_of_nonneg hnorm'.le] at hs
  have hh := (le_div_iff₀ hnorm').mp hs
  have haux : (2 / Real.pi) * |z.arg| * (1 / 2) ≤ |z.im| :=
    (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans hh
  calc
    |z.arg| = Real.pi * ((2 / Real.pi) * |z.arg| * (1 / 2)) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left haux Real.pi_pos.le

private theorem centered_eq_rotation (d r : ℕ) {v : ℝ} :
    centered d r v = ((mass d r v)⁻¹ : ℝ) *
      (rowSum d r v * cis (- (mean d r v * angle d))) := by
  change centered d r v = _ * (raySum d r (rowWeight d) v * _)
  simp only [centered, raySum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [show ((s : ℝ) - mean d r v) * angle d =
    (s : ℝ) * angle d + -(mean d r v * angle d) by ring, cis_add]
  unfold probability
  rw [div_eq_mul_inv, Complex.ofReal_mul]
  change _ * (direction d s * _) = _
  ring

private theorem meanAngle_bounds {d r : ℕ} {v : ℝ} (hrd : r < d) (hv : 0 < v) :
    0 ≤ mean d r v * angle d ∧ mean d r v * angle d < Real.pi := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have ha : 0 < angle d := div_pos Real.pi_pos hd
  have hr' : (r : ℝ) < d := by exact_mod_cast hrd
  refine ⟨mul_nonneg (mean_nonneg d r hv) ha.le, ?_⟩
  calc
    _ ≤ (r : ℝ) * angle d := mul_le_mul_of_nonneg_right (mean_le d r hv) ha.le
    _ < (d : ℝ) * angle d := mul_lt_mul_of_pos_right hr' ha
    _ = Real.pi := by rw [angle, mul_div_cancel₀ _ hd.ne']

private theorem centered_arg {d r : ℕ} {v : ℝ} (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    (centered d r v).arg = (rowSum d r v).arg - mean d r v * angle d := by
  have hm := meanAngle_bounds hrd hv
  have hi := rowSum_im_pos hr hrd hv
  have ha : 0 ≤ (rowSum d r v).arg := Complex.arg_nonneg_iff.mpr hi.le
  have hb := Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
  have hnz : rowSum d r v ≠ 0 := by intro h; simp [h] at hi
  have hcis : (cis (-(mean d r v * angle d))).arg = -(mean d r v * angle d) := by
    rw [cis, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [hm.2], by linarith [hm.1, Real.pi_pos]⟩
  have hab : (rowSum d r v).arg + (cis (-(mean d r v * angle d))).arg ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [hcis]
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
  have hcis0 : cis (-(mean d r v * angle d)) ≠ 0 := Complex.exp_ne_zero _
  rw [centered_eq_rotation, Complex.arg_real_mul _ (inv_pos.mpr (mass_pos d r hv)),
    Complex.arg_mul hnz hcis0 hab, hcis, sub_eq_add_neg]

/-- The actual tilted row-polynomial argument differs from its mean angle by
a constant times the angular variance, uniformly over all positive radii. -/
theorem rowSum_arg_sub_mean_le {d r : ℕ} {v : ℝ} (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    |(rowSum d r v).arg - mean d r v * angle d| ≤
      2 * Real.pi * (variance d r v * angle d ^ 2) := by
  rw [← centered_arg hr hrd hv]
  by_cases h : variance d r v * angle d ^ 2 ≤ 1
  · have hz : 1 / 2 ≤ (centered d r v).re := by
      linarith [centered_re_bound d r hv]
    calc
      |(centered d r v).arg| ≤ Real.pi * |(centered d r v).im| := arg_abs_le_pi_mul_im hz
      _ ≤ Real.pi * (2 * (variance d r v * angle d ^ 2)) :=
        mul_le_mul_of_nonneg_left (centered_im_bound d r hv) Real.pi_pos.le
      _ = _ := by ring
  · calc
      |(centered d r v).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
      _ ≤ 2 * Real.pi * (variance d r v * angle d ^ 2) := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (show 0 ≤ 2 * Real.pi by positivity)
        linarith [Real.pi_pos]

#print axioms rowSum_arg_sub_mean_le

/-- Quantitative phase deviation for the actual balanced-array weights,
before applying the truncated-binomial variance bound. -/
theorem phase_deviation_le_variance (n : ℕ) {d r : ℕ} {v : ℝ}
    (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v) :
    |phase n d r v / Real.pi - (n : ℝ) * mean d r v / d| ≤
      2 * (n : ℝ) * (variance d r v * angle d ^ 2) + ((d : ℝ) - 1) / 2 := by
  let ν : ℝ := ((d : ℝ) - 1) / 2
  let θ : ℝ := (rowSum d r v).arg - mean d r v * angle d
  let ψ : ℝ := (momentSum d r v / rowSum d r v).arg
  have hν : 0 ≤ ν := by
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    exact div_nonneg (sub_nonneg.mpr hd) (by norm_num)
  have heq : phase n d r v / Real.pi - (n : ℝ) * mean d r v / d =
      ((n : ℝ) / Real.pi) * θ - (ν / Real.pi) * ψ := by
    unfold phase θ ψ ν angle
    rw [arg_moment_div_row hr hrd hv]
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp [Real.pi_ne_zero, hd]
    ring
  rw [heq]
  calc
    |((n : ℝ) / Real.pi) * θ - (ν / Real.pi) * ψ| ≤
        ((n : ℝ) / Real.pi) * |θ| + (ν / Real.pi) * |ψ| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le),
        abs_of_nonneg (div_nonneg hν Real.pi_pos.le)]
        using abs_sub_le (((n : ℝ) / Real.pi) * θ) 0 ((ν / Real.pi) * ψ)
    _ ≤ ((n : ℝ) / Real.pi) * (2 * Real.pi * (variance d r v * angle d ^ 2)) +
        (ν / Real.pi) * Real.pi :=
      add_le_add
        (mul_le_mul_of_nonneg_left (rowSum_arg_sub_mean_le hr hrd hv) (by positivity))
        (mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (div_nonneg hν Real.pi_pos.le))
    _ = _ := by
      change _ = _ + ν
      field_simp [Real.pi_ne_zero]
      ring

#print axioms phase_deviation_le_variance

private theorem interpolate_variance {D m V : ℝ} (hD : 1 ≤ D) (hm : 0 ≤ m)
    (hVd : V ≤ D / 4) (hVm : V ≤ m * (1 + m)) :
    V ≤ 2 * Real.sqrt D * m := by
  have hsq := Real.sq_sqrt (show 0 ≤ D by linarith)
  have h1 : 1 ≤ Real.sqrt D := Real.le_sqrt_of_sq_le (by simpa using hD)
  by_cases h : m ≤ Real.sqrt D
  · calc
      V ≤ m * (1 + m) := hVm
      _ ≤ m * (2 * Real.sqrt D) := mul_le_mul_of_nonneg_left (by linarith) hm
      _ = _ := by ring
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h)
      (show 0 ≤ 2 * Real.sqrt D by positivity)
    nlinarith [hVd, hsq]

/-- The stated tilt inequality with explicit constants, conditional only on
the three size-law variance inequalities used in the written proof. -/
theorem phase_deviation_le_min_mean_deficit (n : ℕ) {d r : ℕ} {v : ℝ}
    (hr : 1 ≤ r) (hrd : r < d) (hv : 0 < v)
    (hVd : variance d r v ≤ (d : ℝ) / 4)
    (hVmean : variance d r v ≤ mean d r v * (1 + mean d r v))
    (hVdeficit : variance d r v ≤ ((r : ℝ) - mean d r v) * (1 + ((r : ℝ) - mean d r v))) :
    |phase n d r v / Real.pi - (n : ℝ) * mean d r v / d| ≤
      4 * Real.pi ^ 2 * ((n : ℝ) / d * min (mean d r v) ((r : ℝ) - mean d r v)) /
        Real.sqrt d + ((d : ℝ) - 1) / 2 := by
  let μ := mean d r v
  let h : ℝ := (r : ℝ) - μ
  let m := min μ h
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd0 : (0 : ℝ) < d := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hV : variance d r v ≤ 2 * Real.sqrt d * m := by
    unfold m
    by_cases hm : μ ≤ h
    · rw [min_eq_left hm]
      exact interpolate_variance hd (mean_nonneg d r hv) hVd hVmean
    · rw [min_eq_right (le_of_not_ge hm)]
      exact interpolate_variance hd (sub_nonneg.mpr (mean_le d r hv)) hVd hVdeficit
  refine (phase_deviation_le_variance n hr hrd hv).trans (add_le_add_right ?_ _)
  calc
    2 * (n : ℝ) * (variance d r v * angle d ^ 2) ≤
        2 * (n : ℝ) * ((2 * Real.sqrt d * m) * angle d ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV (sq_nonneg _)) (by positivity)
    _ = 4 * Real.pi ^ 2 * ((n : ℝ) / d * m) / Real.sqrt d := by
      have hs := Real.sq_sqrt hd0.le
      unfold angle
      field_simp [hd0.ne', hsqrt.ne']
      nlinarith only [congrArg (fun x : ℝ => 4 * (n : ℝ) * Real.pi ^ 2 * m * x) hs]

#print axioms phase_deviation_le_min_mean_deficit

end

end BalancedEventual.OccupiedPhase
