import CatalanStrictPeaksBetaMoments

/-!
# Uniform numerical bounds for the Catalan covariance comparison

At sizes at least 150, each of the first four scaled moments is bounded
by its value at 150. The rational estimates use the same integrated
envelopes as (11) and (12) of the proof.
-/

namespace CatalanStrictPeaks.BetaMoments

/-- The average of the one-step tilt. -/
noncomputable def tiltAverage (n : ℕ) : ℝ := ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1)

/-- The integrated moment envelope for the centered tilt on the local interval. -/
noncomputable def tiltedMoment (n j : ℕ) : ℝ :=
  moment n (j + 1) + (3 / (2 * (n : ℝ))) * moment n j

private noncomputable def scaledMoment (n j : ℕ) : ℝ := (n : ℝ) ^ j * moment n j

private theorem scaledMoment_nonneg {n j : ℕ} (hn : 150 ≤ n) (hj : j ≤ 4) :
    0 ≤ scaledMoment n j := by
  have hnN : 0 < n := by omega
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  have hM : 0 ≤ moment n j := by
    rw [moment, rawMoment_gamma (by linarith)]
    exact div_nonneg
      (div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
        (Real.Gamma_pos_of_pos (by linarith)).le) (Real.Gamma_pos_of_pos (by positivity)).le)
      (mass_pos hnN).le
  exact mul_nonneg (by positivity) hM

private theorem scaledMoment_succ {n j : ℕ} (h : (j : ℝ) + 3 / 2 < (n : ℝ)) :
    scaledMoment n (j + 1) =
      ((j : ℝ) + 3 / 2) * ((n : ℝ) / ((n : ℝ) - j - 3 / 2)) * scaledMoment n j := by
  rw [scaledMoment, scaledMoment, moment_succ h, pow_succ]
  ring

private theorem ratio_le_at_150 {x a : ℝ} (hx : 150 ≤ x) (ha : 0 ≤ a) (ha' : a < 150) :
    x / (x - a) ≤ 150 / (150 - a) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx)]

private theorem scaledMoment_le_150 {n j : ℕ} (hn : 150 ≤ n) (hj : j ≤ 4) :
    scaledMoment n j ≤ scaledMoment 150 j := by
  have hnN : 0 < n := by omega
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero =>
    have h0 : moment n 0 = 1 := by rw [moment_product (by simp; linarith)]; simp
    have h150 : moment 150 0 = 1 := by rw [moment_product (by norm_num)]; simp
    simp [scaledMoment, h0, h150]
  | succ j ih =>
    have hjR : (j : ℝ) ≤ 4 := by norm_cast; omega
    have hj₀ : j ≤ 4 := by omega
    have hp : 0 ≤ (j : ℝ) + 3 / 2 := by positivity
    have hratio := ratio_le_at_150 hnR hp (by linarith)
    rw [scaledMoment_succ (by linarith), scaledMoment_succ (by norm_num; linarith)]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hratio hp
    have hc : 0 ≤ ((j : ℝ) + 3 / 2) * (150 / (150 - ((j : ℝ) + 3 / 2))) :=
      mul_nonneg hp (div_nonneg (by positivity) (by linarith))
    rw [show (n : ℝ) - j - 3 / 2 = (n : ℝ) - ((j : ℝ) + 3 / 2) by ring,
      show (150 : ℝ) - j - 3 / 2 = 150 - ((j : ℝ) + 3 / 2) by ring]
    exact mul_le_mul hh (ih hj₀) (scaledMoment_nonneg hn hj₀) hc

private theorem scaled_bounds {n : ℕ} (hn : 150 ≤ n) :
    scaledMoment n 1 ≤ 38 / 25 ∧ scaledMoment n 2 ≤ 193 / 50 ∧
      scaledMoment n 3 ≤ 14 ∧ scaledMoment n 4 ≤ 65 := by
  refine ⟨(scaledMoment_le_150 hn (by decide)).trans ?_,
    (scaledMoment_le_150 hn (by decide)).trans ?_,
    (scaledMoment_le_150 hn (by decide)).trans ?_,
    (scaledMoment_le_150 hn (by decide)).trans ?_⟩
  all_goals
    unfold scaledMoment
    rw [moment_product (by norm_num)]
    norm_num [Finset.prod_range_succ]

private theorem scaled_tiltedMoment {n : ℕ} (hn : 150 ≤ n) (j : ℕ) :
    (n : ℝ) ^ (j + 1) * tiltedMoment n j =
      scaledMoment n (j + 1) + (3 / 2) * scaledMoment n j := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (n : ℝ) ≠ 0 := by linarith
  unfold scaledMoment tiltedMoment
  rw [pow_succ]
  field_simp [hx]
  ring

private theorem scaled_tilted_bounds {n : ℕ} (hn : 150 ≤ n) :
    (n : ℝ) ^ 2 * tiltedMoment n 1 ≤ 307 / 50 ∧
      (n : ℝ) ^ 3 * tiltedMoment n 2 ≤ 1979 / 100 ∧
      (n : ℝ) ^ 4 * tiltedMoment n 3 ≤ 86 := by
  obtain ⟨h1, h2, h3, h4⟩ := scaled_bounds hn
  refine ⟨?_, ?_, ?_⟩
  · rw [show (2 : ℕ) = 1 + 1 by decide, scaled_tiltedMoment hn]
    linarith
  · rw [show (3 : ℕ) = 2 + 1 by decide, scaled_tiltedMoment hn]
    linarith
  · rw [show (4 : ℕ) = 3 + 1 by decide, scaled_tiltedMoment hn]
    linarith

/-- On the effective range, the tilt mean exceeds 99 percent. -/
theorem tiltAverage_ge {n : ℕ} (hn : 150 ≤ n) : 99 / 100 ≤ tiltAverage n := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold tiltAverage
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

/-- The numerical bound contributed by the Lipschitz factor after applying the tilt. -/
theorem conjugate_moment_gap_bound {n : ℕ} (hn : 150 ≤ n) :
    ((n : ℝ) / 8) * (moment n 1 - moment (n + 1) 1) ≤ 1 / (4 * (n : ℝ)) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn' : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : 0 < (n : ℝ) - 3 / 2 := by linarith
  have h2 : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hs : (3 / 2 : ℝ) < (n + 1 : ℕ) := by push_cast; linarith
  rw [moment_one (by linarith), moment_one hs, Nat.cast_add, Nat.cast_one,
    show (n : ℝ) + 1 - 3 / 2 = (n : ℝ) - 1 / 2 by ring]
  have hgap : (3 / 2 : ℝ) / ((n : ℝ) - 3 / 2) - (3 / 2) / ((n : ℝ) - 1 / 2) =
      (3 / 2) / (((n : ℝ) - 3 / 2) * ((n : ℝ) - 1 / 2)) := by
    set a := (n : ℝ) - 3 / 2
    set b := (n : ℝ) - 1 / 2
    field_simp [show a ≠ 0 from h1.ne', show b ≠ 0 from h2.ne']
    dsimp [a, b]
    ring
  rw [hgap, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos h1 h2) (by positivity)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show 0 ≤ (n : ℝ) - 10 by linarith)]

/-- The local cubic comparison and the affine tail leave a strict margin
of at most three quarters of the target successive-size bound. -/
theorem small_covariance_numeric {n : ℕ} (hn : 150 ≤ n) :
    (11 * tiltedMoment n 1 + (1 + 11 * (n : ℝ) / 8) * tiltedMoment n 2 +
      (n : ℝ) / 8 * tiltedMoment n 3 + 1 / (20 * (n : ℝ))) / tiltAverage n <
      3 / (4 * (n : ℝ)) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  let T1 := (n : ℝ) ^ 2 * tiltedMoment n 1
  let T2 := (n : ℝ) ^ 3 * tiltedMoment n 2
  let T3 := (n : ℝ) ^ 4 * tiltedMoment n 3
  obtain ⟨b1, b2, b3⟩ := scaled_tilted_bounds hn
  have hEq : (n : ℝ) * (11 * tiltedMoment n 1 +
      (1 + 11 * (n : ℝ) / 8) * tiltedMoment n 2 +
      (n : ℝ) / 8 * tiltedMoment n 3 + 1 / (20 * (n : ℝ))) =
    11 * y * T1 + ((y + 11 / 8) * y) * T2 + (y ^ 2 / 8) * T3 + 1 / 20 := by
    dsimp [y, T1, T2, T3]
    field_simp [hx.ne']
    ring
  have hq : 0 < tiltAverage n := lt_of_lt_of_le (by norm_num) (tiltAverage_ge hn)
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ (y + 11 / 8) * y by positivity)
  have hC := mul_le_mul_of_nonneg_left b3 (show 0 ≤ y ^ 2 / 8 by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  have hbound : 11 * y * T1 + ((y + 11 / 8) * y) * T2 + (y ^ 2 / 8) * T3 + 1 / 20
      < (3 / 4) * tiltAverage n := by
    change 11 * y * _ ≤ _ at hA
    change ((y + 11 / 8) * y) * _ ≤ _ at hB
    change (y ^ 2 / 8) * _ ≤ _ at hC
    dsimp only [T1, T2, T3]
    nlinarith only [hA, hB, hC, hy', hyy, tiltAverage_ge hn]
  apply (div_lt_div_iff₀ hq (by positivity : 0 < 4 * (n : ℝ))).mpr
  nlinarith only [hEq, hbound]

/-- The full local quadratic comparison and the tail are below the
successive-size allowance in (12). -/
theorem broad_covariance_numeric {n : ℕ} (hn : 150 ≤ n) :
    ((((n : ℝ) / 2 + 11) * tiltedMoment n 1 +
      ((n : ℝ) / 2 + 1) * tiltedMoment n 2 + 1 / (20 * (n : ℝ))) / tiltAverage n) <
      4 / (n : ℝ) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  let T1 := (n : ℝ) ^ 2 * tiltedMoment n 1
  let T2 := (n : ℝ) ^ 3 * tiltedMoment n 2
  obtain ⟨b1, b2, _⟩ := scaled_tilted_bounds hn
  have hEq : (n : ℝ) * (((n : ℝ) / 2 + 11) * tiltedMoment n 1 +
      ((n : ℝ) / 2 + 1) * tiltedMoment n 2 + 1 / (20 * (n : ℝ))) =
    (1 / 2 + 11 * y) * T1 + ((1 / 2 + y) * y) * T2 + 1 / 20 := by
    dsimp [y, T1, T2]
    field_simp [hx.ne']
    ring
  have hq : 0 < tiltAverage n := lt_of_lt_of_le (by norm_num) (tiltAverage_ge hn)
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 1 / 2 + 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ (1 / 2 + y) * y by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  have hbound : (1 / 2 + 11 * y) * T1 + ((1 / 2 + y) * y) * T2 + 1 / 20 <
      4 * tiltAverage n := by
    dsimp only [T1, T2]
    nlinarith only [hA, hB, hy', hyy, tiltAverage_ge hn]
  apply (div_lt_div_iff₀ hq hx).mpr
  nlinarith only [hEq, hbound]

/-- The cubic loss in the real-part estimate (10) is below three twentieths. -/
theorem small_real_part_numeric {n : ℕ} (hn : 150 ≤ n) :
    11 * moment n 1 + (1 + 11 * (n : ℝ) / 8) * moment n 2 +
      (n : ℝ) / 8 * moment n 3 + 1 / (20 * (n : ℝ)) < 3 / 20 := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  obtain ⟨b1, b2, b3, _⟩ := scaled_bounds hn
  have heq :
      11 * moment n 1 + (1 + 11 * (n : ℝ) / 8) * moment n 2 +
        (n : ℝ) / 8 * moment n 3 + 1 / (20 * (n : ℝ)) =
        (11 * y) * scaledMoment n 1 + (y ^ 2 + 11 * y / 8) * scaledMoment n 2 +
          (y ^ 2 / 8) * scaledMoment n 3 + y / 20 := by
    dsimp [y, scaledMoment]
    field_simp [hx.ne']
    ring
  rw [heq]
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ y ^ 2 + 11 * y / 8 by positivity)
  have hC := mul_le_mul_of_nonneg_left b3 (show 0 ≤ y ^ 2 / 8 by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  nlinarith only [hA, hB, hC, hy', hyy]

end CatalanStrictPeaks.BetaMoments
