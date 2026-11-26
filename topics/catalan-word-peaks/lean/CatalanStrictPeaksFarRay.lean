import CatalanStrictPeaksRayTransfer
import CatalanStrictPeaksNearAmplitude

/-!
# The far Catalan ray

The estimate uses the norm of the actual prefactor in the coefficient formula,
the first radial beta moment, and the distances between the four branch points.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex MeasureTheory Set
open scoped ComplexConjugate

private theorem norm_cutFactor_sq (z x : ℂ) :
    ‖cutFactor z x‖ ^ 2 = ‖1 - x / z‖ := by
  rw [← norm_pow]
  exact congrArg norm (principalRoot_sq (1 - x / z))

private theorem norm_cutFactor_radial {w z : ℂ} (hz : z ≠ 0) (hwz : w ≠ z)
    {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) (hb : ‖w / (w - z)‖ ≤ L) :
    ‖cutFactor z (w * (1 + (s : ℂ)))‖ ≤
      ‖cutFactor z w‖ * Real.sqrt (1 + L * s) := by
  have hfactor : 1 - w * (1 + (s : ℂ)) / z =
      (1 - w / z) * (1 + (w / (w - z)) * (s : ℂ)) := by
    field_simp [hz, sub_ne_zero.mpr hwz]
    ring
  have hbound : ‖1 + (w / (w - z)) * (s : ℂ)‖ ≤ 1 + L * s := calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(w / (w - z)) * (s : ℂ)‖ := norm_add_le _ _
    _ = 1 + ‖w / (w - z)‖ * s := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ _ := by gcongr
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_cutFactor_sq, hfactor, norm_mul, mul_pow, norm_cutFactor_sq,
    Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

private theorem sqrt_affine_le {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) :
    Real.sqrt (1 + L * s) ≤ 1 + L * s / 2 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (L * s)]

private theorem real_sub_norm_sq (c : ℝ) (z : ℂ) :
    ‖(c : ℂ) - z‖ ^ 2 = c ^ 2 + ‖z‖ ^ 2 - 2 * c * z.re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem real_sub_norm_radial_le {c : ℝ} {z : ℂ} {s : ℝ}
    (hc : 0 ≤ c) (hz : z.re ≤ 0) (hs : 0 ≤ s) :
    ‖(c : ℂ) - z‖ ≤ ‖(c : ℂ) - z * (1 + (s : ℂ))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [real_sub_norm_sq, real_sub_norm_sq, norm_mul,
    show (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) by push_cast <;> rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hpow : ‖z‖ ^ 2 ≤ (‖z‖ * (1 + s)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (by nlinarith [norm_nonneg z])
  have hre := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc hs) hz
  nlinarith

private theorem rayPrefactor_far_form (d : ℝ) (x : ℂ) :
    rayPrefactor d 1 x =
      -(cutFactor (nearPoint d) x * cutFactor (conj (nearPoint d)) x *
        cutFactor (conj (farPoint d)) x) / (2 * x * ((scale d : ℂ) - x)) := by
  have h : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  rw [rayPrefactor, h]
  simp [cutPoint, Finset.prod_insert]
  ring

/-- The actual upper far-ray prefactor satisfies the affine envelope. -/
theorem farRay_prefactor_norm_le {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hnd : 2 ≤ (n : ℝ) * d) (hs : 0 ≤ s) :
    ‖rayPrefactor d 1 (farPoint d * (1 + (s : ℂ)))‖ ≤
      ‖rayPrefactor d 1 (farPoint d)‖ * (1 + (1 + (n : ℝ) / 4) * s / 2) := by
  let w := farPoint d
  let z := nearPoint d
  let c : ℂ := (scale d : ℂ)
  let x := w * (1 + (s : ℂ))
  let L : ℝ := 1 + (n : ℝ) / 4
  have hzr : 0 < z.re := nearPoint_re_pos hd
  have hwr : w.re < 0 := farPoint_re_neg hd
  have hwi : 0 < w.im := farPoint_im_pos hd hD
  have hz : z ≠ 0 := fun h => by simpa [h] using hzr
  have hw : w ≠ 0 := fun h => by simpa [h] using hwr
  have hzc : conj z ≠ 0 := fun h => hz (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hwc : conj w ≠ 0 := fun h => hw (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hwz : w ≠ z := fun h => by rw [h] at hwr; linarith
  have hwzc : w ≠ conj z := fun h => by rw [h, Complex.conj_re] at hwr; linarith
  have hwwc : w ≠ conj w := fun h =>
    by have he := congrArg Complex.im h; rw [Complex.conj_im] at he; linarith
  have hc : 0 < scale d := scale_pos hd
  have hcw : c - w ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    change scale d = w.re at he
    linarith
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hdirect : ‖w / (w - z)‖ ≤ L := by
    refine (far_to_near_bound hd hD).trans ?_
    change 1 + 1 / (2 * d) ≤ 1 + (n : ℝ) / 4
    apply add_le_add_left
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).2
    nlinarith
  have hA : ‖cutFactor z x‖ ≤ ‖cutFactor z w‖ * (1 + L * s / 2) :=
    (norm_cutFactor_radial hz hwz hs hL hdirect).trans
      (mul_le_mul_of_nonneg_left (sqrt_affine_le hs hL) (norm_nonneg _))
  have hB : ‖cutFactor (conj z) x‖ ≤ ‖cutFactor (conj z) w‖ * Real.sqrt (1 + s) := by
    simpa only [one_mul] using
      norm_cutFactor_radial hzc hwzc hs zero_le_one (opposite_cross_bounds hd hD).2
  have hC : ‖cutFactor (conj w) x‖ ≤ ‖cutFactor (conj w) w‖ * Real.sqrt (1 + s) := by
    simpa only [one_mul] using norm_cutFactor_radial hwc hwwc hs zero_le_one
      (far_conjugate_bound hd hD)
  have hprod :
      ‖cutFactor z x‖ * ‖cutFactor (conj z) x‖ * ‖cutFactor (conj w) x‖ ≤
        (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
          (1 + L * s / 2) * (1 + s) := calc
    _ ≤ (‖cutFactor z w‖ * (1 + L * s / 2)) *
          (‖cutFactor (conj z) w‖ * Real.sqrt (1 + s)) *
          (‖cutFactor (conj w) w‖ * Real.sqrt (1 + s)) := by gcongr
    _ = (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * Real.sqrt (1 + s) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hx : ‖x‖ = ‖w‖ * (1 + s) := by
    rw [show x = w * ((1 + s : ℝ) : ℂ) by dsimp [x]; push_cast <;> rfl, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hdist : ‖c - w‖ ≤ ‖c - x‖ := real_sub_norm_radial_le hc.le hwr.le hs
  have hden : 0 < 2 * ‖w‖ * ‖c - w‖ := by
    exact mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hw)) (norm_pos_iff.mpr hcw)
  have hden' : 0 < 2 * ‖x‖ * ‖c - x‖ := by
    rw [hx]
    exact mul_pos (mul_pos (by norm_num)
      (mul_pos (norm_pos_iff.mpr hw) (by positivity))) ((norm_pos_iff.mpr hcw).trans_le hdist)
  change ‖rayPrefactor d 1 x‖ ≤ ‖rayPrefactor d 1 w‖ * (1 + L * s / 2)
  simp only [rayPrefactor_far_form, norm_div, norm_neg, norm_mul, Complex.norm_two]
  calc
    _ ≤ (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * (1 + s) / (2 * ‖x‖ * ‖c - x‖) :=
      div_le_div_of_nonneg_right hprod hden'.le
    _ ≤ (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * (1 + s) / (2 * ‖x‖ * ‖c - w‖) := by
      apply div_le_div_of_nonneg_left (by positivity) _ (by gcongr)
      rw [hx]
      positivity
    _ = _ := by
      rw [hx]
      field_simp [(norm_pos_iff.mpr hw).ne', (norm_pos_iff.mpr hcw).ne',
        (show 1 + s ≠ 0 by positivity)]
      ring

private theorem norm_rayIntegrand {d : ℝ} {n : ℕ} {j : Fin 4} {s : ℝ} (hs : 0 ≤ s) :
    ‖rayIntegrand d n j s‖ = BetaMoments.rayWeight n s *
      ‖rayPrefactor d j (cutPoint d j * (1 + (s : ℂ)))‖ := by
  rw [rayIntegrand, BetaMoments.rayWeight, norm_mul, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    show (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) by push_cast <;> rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_pow, div_eq_mul_inv]

/-- The actual far-ray integral is bounded by its endpoint times six fifths
of the mass of the radial density. -/
theorem farRay_integral_norm_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 2 ≤ (n : ℝ) * d) :
    ‖∫ s in Ioi (0 : ℝ), rayIntegrand d n 1 s‖ ≤
      (6 / 5 : ℝ) * BetaMoments.mass n * ‖rayPrefactor d 1 (farPoint d)‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let A := ‖rayPrefactor d 1 (farPoint d)‖
  let B : ℝ := (1 + (n : ℝ) / 4) / 2
  obtain ⟨henv, hmoment⟩ := BetaMoments.affine_moment (n := n) (by linarith) A (A * B)
  have hmon : ∀ s ∈ Ioi (0 : ℝ), ‖rayIntegrand d n 1 s‖ ≤
      (A + A * B * s) * BetaMoments.rayWeight n s := by
    intro s hs
    have hs0 : 0 < s := hs
    rw [norm_rayIntegrand hs0.le]
    change BetaMoments.rayWeight n s *
      ‖rayPrefactor d 1 (farPoint d * (1 + (s : ℂ)))‖ ≤ _
    calc
      _ ≤ BetaMoments.rayWeight n s * (A * (1 + (1 + (n : ℝ) / 4) * s / 2)) :=
        mul_le_mul_of_nonneg_left (farRay_prefactor_norm_le hd hD hnd hs0.le)
          (BetaMoments.rayWeight_nonneg n hs0.le)
      _ = _ := by dsimp [B]; ring
  calc
    _ ≤ ∫ s in Ioi (0 : ℝ), ‖rayIntegrand d n 1 s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi (0 : ℝ), (A + A * B * s) * BetaMoments.rayWeight n s :=
      setIntegral_mono_on (rayIntegrand_integrable hd hD hn0 1).norm henv measurableSet_Ioi hmon
    _ = BetaMoments.mass n * (A + A * B * BetaMoments.moment n 1) := hmoment
    _ = BetaMoments.mass n * A * (1 + B * BetaMoments.moment n 1) := by ring
    _ ≤ _ := by
      have hnum : 1 + B * BetaMoments.moment n 1 ≤ (6 / 5 : ℝ) := by
        rw [BetaMoments.moment_one (by linarith)]
        dsimp [B]
        have hp : 0 < (n : ℝ) - 3 / 2 := by linarith
        apply (le_of_sub_nonneg)
        rw [show (6 / 5 : ℝ) - (1 + (1 + (n : ℝ) / 4) / 2 *
            ((3 / 2) / ((n : ℝ) - 3 / 2))) =
            ((n : ℝ) / 80 - 21 / 20) / ((n : ℝ) - 3 / 2) by field_simp [hp.ne']; ring]
        exact div_nonneg (by linarith) hp.le
      rw [show (6 / 5 : ℝ) * BetaMoments.mass n * A =
        BetaMoments.mass n * A * (6 / 5) by ring]
      exact mul_le_mul_of_nonneg_left hnum
        (mul_nonneg (BetaMoments.mass_pos hn0).le (norm_nonneg _))

end CatalanStrictPeaks.CutGeometry
