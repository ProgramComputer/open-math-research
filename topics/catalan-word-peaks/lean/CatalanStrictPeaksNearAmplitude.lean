import CatalanStrictPeaksRayTransfer
import CatalanStrictPeaksCutBounds
import CatalanStrictPeaksBetaMoments

/-!
# The normalized amplitude on the dominant Catalan cut

The separate square-root ratios come from the actual principal cut factors.
Their squares and positive real parts allow the pointwise estimates to be
applied to the integrand from the Cauchy deformation.
-/

namespace CatalanStrictPeaks.CutGeometry

open Set Complex MeasureTheory
open scoped ComplexConjugate

private theorem principalRoot_re_pos {u : ℂ} (hu : u ∈ slitPlane) :
    0 < (principalRoot u).re := by
  have harg := (mem_slitPlane_iff_arg.mp hu).1.lt_of_le (arg_le_pi u)
  have harg' := neg_pi_lt_arg u
  unfold principalRoot
  rw [cpow_def_of_ne_zero (mem_slitPlane_iff_arg.mp hu).2, exp_re]
  have him : (log u * (2 : ℂ)⁻¹).im = u.arg / 2 := by
    rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
    simp [mul_im, log_im]
    ring
  rw [him]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

private theorem one_sub_radial_slit {q : ℂ} (hq : q.im ≠ 0 ∨ q.re < 0)
    {t : ℝ} (ht : 0 < t) : 1 - q * (t : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases hq with h | h
  · right
    simpa [sub_im, mul_im] using mul_ne_zero h ht.ne'
  · left
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    linarith [mul_neg_of_neg_of_pos h ht]

/-- The normalized ratio of the same principal cut factor along a positive
radial step. The branch choice forces the ratio to have positive real part. -/
private theorem rootRatio_re_pos {q : ℂ} (hq : q.im ≠ 0 ∨ q.re < 0)
    {t : ℝ} (ht : 0 < t) :
    0 < (principalRoot (1 - q * (t : ℂ)) / principalRoot (1 - q)).re := by
  let g := principalRoot (1 - q * (t : ℂ))
  let h := principalRoot (1 - q)
  have hg : 0 < g.re := principalRoot_re_pos (one_sub_radial_slit hq ht)
  have hh : 0 < h.re := principalRoot_re_pos (by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one)
  have hs : 2 * g.re * g.im = -(q.im * t) := by
    have he := congrArg Complex.im (principalRoot_sq (1 - q * (t : ℂ)))
    calc
      _ = g.re * g.im + g.im * g.re := by ring
      _ = _ := by simpa only [g, pow_two, mul_im, sub_im, one_im, ofReal_re,
        ofReal_im, mul_zero, zero_add, zero_sub] using he
  have h₀ : 2 * h.re * h.im = -q.im := by
    have he := congrArg Complex.im (principalRoot_sq (1 - q))
    calc
      _ = h.re * h.im + h.im * h.re := by ring
      _ = _ := by simpa only [h, pow_two, mul_im, sub_im, one_im, zero_sub] using he
  have him : 0 ≤ g.im * h.im := by
    have hprod : 0 ≤ (2 * g.re * (2 * h.re)) * (g.im * h.im) := by
      rw [show (2 * g.re * (2 * h.re)) * (g.im * h.im) =
        (2 * g.re * g.im) * (2 * h.re * h.im) by ring, hs, h₀]
      rw [show -(q.im * t) * -q.im = q.im ^ 2 * t by ring]
      positivity
    exact nonneg_of_mul_nonneg_right hprod (by positivity : 0 < 2 * g.re * (2 * h.re))
  have hne : h ≠ 0 := by
    intro hz
    simp [hz] at hh
  have hnorm := Complex.normSq_pos.mpr hne
  change 0 < (g / h).re
  rw [div_eq_mul_inv, mul_re, inv_re, inv_im, neg_div, mul_neg, sub_neg_eq_add,
    ← mul_div_assoc, ← mul_div_assoc]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hg hh) hnorm) (div_nonneg him hnorm.le)

private noncomputable def rootRatio (z w : ℂ) (s : ℝ) : ℂ :=
  cutFactor w (z * (1 + (s : ℂ))) / cutFactor w z

private noncomputable def denominatorCoefficient (d : ℝ) : ℂ :=
  nearPoint d / (nearPoint d - (scale d : ℂ))

private noncomputable def otherRoots (d : ℝ) (x : ℂ) : ℂ :=
  cutFactor (conj (nearPoint d)) x *
    (cutFactor (farPoint d) x * cutFactor (conj (farPoint d)) x)

private theorem rayPrefactor_near_form (d : ℝ) (x : ℂ) :
    rayPrefactor d 0 x = -otherRoots d x / (2 * x * ((scale d : ℂ) - x)) := by
  have h : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  rw [rayPrefactor, h, otherRoots]
  simp [cutPoint, Finset.prod_insert]
  ring

/-- The near-ray amplitude normalized at the branch point. -/
noncomputable def nearAmplitude (d s : ℝ) : ℂ :=
  rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) / rayPrefactor d 0 (nearPoint d)

private noncomputable def otherRootRatios (d s : ℝ) : ℂ :=
  rootRatio (nearPoint d) (conj (nearPoint d)) s *
    (rootRatio (nearPoint d) (farPoint d) s * rootRatio (nearPoint d) (conj (farPoint d)) s)

private theorem rootRatio_sq_re {z w : ℂ} (hw : w ≠ 0)
    (hq : (z / w).im ≠ 0 ∨ (z / w).re < 0) {s : ℝ} (hs : 0 ≤ s) :
    rootRatio z w s ^ 2 = 1 + z / (z - w) * (s : ℂ) ∧ 0 < (rootRatio z w s).re := by
  have hq₀ : 1 - z / w ∈ slitPlane := by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one
  have hne := (mem_slitPlane_iff_arg.mp hq₀).2
  have hwz : z - w ≠ 0 := by
    intro hz
    have hw' : z = w := sub_eq_zero.mp hz
    simp [hw', hw] at hne
  constructor
  · rw [rootRatio, div_pow, cutFactor, cutFactor, principalRoot_sq, principalRoot_sq]
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hwz).symm
    field_simp [hw, hwz, hwz', hne]
    ring
  · have ht : 0 < 1 + s := by positivity
    unfold rootRatio cutFactor
    rw [show z * (1 + (s : ℂ)) / w = z / w * ((1 + s : ℝ) : ℂ) by push_cast; ring]
    exact rootRatio_re_pos hq ht

private theorem near_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) : nearPoint d ≠ 0 := by
  intro h
  simpa [h] using nearPoint_im_pos hd hD

private theorem far_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) : farPoint d ≠ 0 := by
  intro h
  simpa [h] using farPoint_im_pos hd hD

private theorem near_div_conj_near_im {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < (nearPoint d / conj (nearPoint d)).im := by
  have hC : conj (nearPoint d) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 (near_ne_zero hd hD)
  have hnorm := Complex.normSq_pos.mpr hC
  have hRe := nearPoint_re_pos hd
  have hIm := nearPoint_im_pos hd hD
  rw [div_eq_mul_inv, mul_im, inv_re, inv_im, conj_re, conj_im, neg_neg]
  positivity

private theorem near_div_far_im {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    (nearPoint d / farPoint d).im < 0 := by
  have hnorm := Complex.normSq_pos.mpr (far_ne_zero hd hD)
  rw [div_eq_mul_inv, mul_im, inv_re, inv_im]
  exact add_neg
    (mul_neg_of_pos_of_neg (nearPoint_re_pos hd)
      (div_neg_of_neg_of_pos (neg_neg_of_pos (farPoint_im_pos hd hD)) hnorm))
    (mul_neg_of_pos_of_neg (nearPoint_im_pos hd hD)
      (div_neg_of_neg_of_pos (farPoint_re_neg hd) hnorm))

private theorem near_div_conj_far_re {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    (nearPoint d / conj (farPoint d)).re < 0 := by
  have hnorm := Complex.normSq_pos.mpr ((map_ne_zero (starRingEnd ℂ)).2 (far_ne_zero hd hD))
  rw [div_eq_mul_inv, mul_re, inv_re, inv_im, conj_re, conj_im, neg_neg]
  apply sub_neg.mpr
  exact (mul_neg_of_pos_of_neg (nearPoint_re_pos hd)
    (div_neg_of_neg_of_pos (farPoint_re_neg hd) hnorm)).trans
    (mul_pos (nearPoint_im_pos hd hD) (div_pos (farPoint_im_pos hd hD) hnorm))

private theorem cutFactor_ne_of_ratio {z w : ℂ} (hq : (z / w).im ≠ 0 ∨ (z / w).re < 0) :
    cutFactor w z ≠ 0 := by
  have hp : 0 < (cutFactor w z).re := principalRoot_re_pos (by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one)
  intro hz
  simp [hz] at hp

private theorem otherRoots_ne {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    otherRoots d (nearPoint d) ≠ 0 := by
  unfold otherRoots
  exact mul_ne_zero (cutFactor_ne_of_ratio (Or.inl (near_div_conj_near_im hd hD).ne'))
    (mul_ne_zero (cutFactor_ne_of_ratio (Or.inl (near_div_far_im hd hD).ne))
      (cutFactor_ne_of_ratio (Or.inr (near_div_conj_far_re hd hD))))

private theorem near_mul_real_im {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    (ht : 0 < t) : 0 < (nearPoint d * (t : ℂ)).im := by
  simpa only [mul_im, ofReal_im, mul_zero, zero_add, ofReal_re] using
    mul_pos (nearPoint_im_pos hd hD) ht

private theorem near_sub_scale_ne {d t : ℝ} (hd : 0 < d) (hD : d < 1) (ht : 0 < t) :
    nearPoint d * (t : ℂ) - (scale d : ℂ) ≠ 0 := by
  have hp := near_mul_real_im hd hD ht
  intro hz
  have h := congrArg Complex.im hz
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at h
  exact hp.ne' h

private theorem nearAmplitude_factorization {d s : ℝ} (hd : 0 < d) (hD : d < 1)
    (hs : 0 ≤ s) :
    nearAmplitude d s = CutBounds.shortReciprocal (denominatorCoefficient d) s *
      otherRootRatios d s := by
  let z := nearPoint d
  let c := (scale d : ℂ)
  let x := z * (1 + (s : ℂ))
  have hz : z ≠ 0 := near_ne_zero hd hD
  have hs' : 0 < 1 + s := by positivity
  have ht : 1 + (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
  have hzc : z - c ≠ 0 := by
    simpa [z, c] using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  have hxc : x - c ≠ 0 := by
    simpa [z, c, x] using near_sub_scale_ne hd hD hs'
  have hden : 1 + denominatorCoefficient d * (s : ℂ) = (x - c) / (z - c) := by
    change 1 + z / (z - c) * (s : ℂ) = (x - c) / (z - c)
    field_simp [hzc]
    simp only [x]
    ring
  have hprod : otherRootRatios d s = otherRoots d x / otherRoots d z := by
    simp only [otherRootRatios, otherRoots, rootRatio, z, x, div_mul_div_comm]
  have hO : otherRoots d z ≠ 0 := otherRoots_ne hd hD
  simp only [nearAmplitude, rayPrefactor_near_form, CutBounds.shortReciprocal, hden, hprod]
  change (-otherRoots d x / (2 * x * (c - x))) / (-otherRoots d z / (2 * z * (c - z))) =
    (1 + (s : ℂ))⁻¹ * ((x - c) / (z - c))⁻¹ * (otherRoots d x / otherRoots d z)
  have hcz : c - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hzc).symm
  have hcx : c - x ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hxc).symm
  have hx : x ≠ 0 := mul_ne_zero hz ht
  field_simp [hO, hx, hz, hzc, hxc, hcz, hcx, ht]
  simp only [x]
  ring

private theorem sine_pos {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < Real.sqrt (1 - d ^ 2) := Real.sqrt_pos.mpr (by nlinarith)

private theorem sine_ge_half {d : ℝ} (hd : 0 < d) (hD : d ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.sqrt (1 - d ^ 2) := by
  apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - d ^ 2)]
  nlinarith [mul_nonneg hd.le (show 0 ≤ 1 / 2 - d by linarith)]

private theorem rootRatios_majorants {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) :
    ‖otherRootRatios d s‖ ≤ (1 + s) * (1 + (n : ℝ) * s / 8) ∧
      ‖otherRootRatios d s - 1‖ ≤ ((n : ℝ) / 4 + 2) * s +
        ((n : ℝ) / 4 + 1 / 2) * s ^ 2 := by
  let z := nearPoint d
  let w := farPoint d
  let k := Real.sqrt (1 - d ^ 2)
  have hk : 0 < k := sine_pos hd hD
  have hc : ‖z / (z - conj z)‖ = 1 / (2 * k) := near_conjugate_coefficient hd hD
  have hw : ‖z / (z - w)‖ ≤ 1 / (2 * d) := near_to_far_bound hd hD
  have hh : ‖z / (z - conj w)‖ ≤ 1 := (opposite_cross_bounds hd hD).1
  have hgC := rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (near_ne_zero hd hD))
    (Or.inl (near_div_conj_near_im hd hD).ne') hs
  have hgW := rootRatio_sq_re (far_ne_zero hd hD) (Or.inl (near_div_far_im hd hD).ne) hs
  have hgH := rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (far_ne_zero hd hD))
    (Or.inr (near_div_conj_far_re hd hD)) hs
  have hlong (k : ℝ) (hk : 0 < k) (h : 2 ≤ (n : ℝ) * k) :
      1 / (2 * k) ≤ (n : ℝ) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * k)).mpr
    linarith
  have hshort (k : ℝ) (hk : 1 / 2 ≤ k) : 1 / (2 * k) ≤ 1 :=
    (div_le_one (by linarith : 0 < 2 * k)).mpr (by linarith)
  by_cases h : 1 / 2 ≤ d
  · obtain ⟨hm, he⟩ := CutBounds.three_factor_majorants hs (by positivity : 0 ≤ (n : ℝ) / 4)
      (hc.le.trans (hlong k hk hS)) (hw.trans (hshort d h)) hh
      hgC.1 hgW.1 hgH.1 hgC.2.le hgW.2.le hgH.2.le
    exact ⟨hm.trans_eq (by ring), he⟩
  · have hK : 1 / 2 ≤ k := sine_ge_half hd (le_of_not_ge h)
    obtain ⟨hm, he⟩ := CutBounds.three_factor_majorants hs (by positivity : 0 ≤ (n : ℝ) / 4)
      (hw.trans (hlong d hd hL)) (hc.le.trans (hshort k hK)) hh
      hgW.1 hgC.1 hgH.1 hgW.2.le hgC.2.le hgH.2.le
    rw [mul_left_comm (rootRatio _ _ _)] at hm he
    exact ⟨hm.trans_eq (by ring), he⟩

private theorem near_im_radius {d : ℝ} (hd : 0 < d) :
    (nearPoint d).im = radius d * Real.sqrt (1 - d ^ 2) := by
  change Real.sqrt (radius d ^ 2 - (radius d * d) ^ 2) = _
  rw [show radius d ^ 2 - (radius d * d) ^ 2 = radius d ^ 2 * (1 - d ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (radius_pos hd.le).le]

private theorem scale_mul_radius_factor {d : ℝ} (hd : 0 < d) :
    scale d * (1 + 2 * d) = (2 * d ^ 2 * (1 + d)) * radius d := by
  unfold scale
  calc
    _ = (2 * d ^ 2 * (1 + d) * radius d) * (radius d ^ 2 * (1 + 2 * d)) := by ring
    _ = _ := by rw [radius_relation hd.le, mul_one]

private theorem radius_le_three_scale {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (h : 1 / 2 ≤ d) : radius d ≤ 3 * scale d := by
  have hd₂ : 1 / 4 ≤ d ^ 2 := by nlinarith [mul_nonneg hd.le (show 0 ≤ d - 1 / 2 by linarith)]
  have hnum : 1 + 2 * d ≤ 6 * d ^ 2 * (1 + d) := by
    calc
      _ ≤ 3 / 2 * (1 + d) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  apply (mul_le_mul_right (by positivity : 0 < 1 + 2 * d)).mp
  calc
    _ ≤ radius d * (6 * d ^ 2 * (1 + d)) :=
      mul_le_mul_of_nonneg_left hnum (radius_pos hd.le).le
    _ = 3 * ((2 * d ^ 2 * (1 + d)) * radius d) := by ring
    _ = _ := by rw [← scale_mul_radius_factor hd]; ring

private theorem scale_le_two_radius {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    scale d ≤ 2 * radius d := by
  have hd₂ : d ^ 2 ≤ 1 := by nlinarith
  have hnum : 2 * d ^ 2 * (1 + d) ≤ 2 * (1 + 2 * d) := by
    calc
      _ ≤ 2 * (1 + d) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by linarith
  apply (mul_le_mul_right (by positivity : 0 < 1 + 2 * d)).mp
  rw [scale_mul_radius_factor hd]
  calc
    _ ≤ (2 * (1 + 2 * d)) * radius d := mul_le_mul_of_nonneg_right hnum (radius_pos hd.le).le
    _ = _ := by ring

private theorem near_distance_sine {d : ℝ} (hd : 0 < d) (hD : d < 1) (t : ℝ) :
    scale d * Real.sqrt (1 - d ^ 2) ≤ ‖nearPoint d * (t : ℂ) - (scale d : ℂ)‖ := by
  let a := radius d
  let c := scale d
  let k := Real.sqrt (1 - d ^ 2)
  have hk : d ^ 2 + k ^ 2 = 1 := by
    dsimp [k]
    rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - d ^ 2)]
    ring
  have hc : 0 < c := scale_pos hd
  have hkn : 0 ≤ k := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hc.le hkn) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, sub_im, Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im,
    mul_zero, sub_zero, zero_add, near_im_radius hd]
  change (c * k) ^ 2 ≤ (a * d * t - c) * (a * d * t - c) + (a * k * t) * (a * k * t)
  calc
    _ ≤ (a * t - c * d) ^ 2 + (c * k) ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
    _ = (a * d * t - c) ^ 2 + (a * k * t) ^ 2 +
        (c ^ 2 - (a * t) ^ 2) * (d ^ 2 + k ^ 2 - 1) := by ring
    _ = _ := by rw [hk]; ring

private theorem reciprocal_global {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hs : 0 ≤ s) :
    ‖CutBounds.shortReciprocal (denominatorCoefficient d) s‖ ≤
      2 * (n : ℝ) / (1 + s) := by
  let z := nearPoint d
  let c := scale d
  let a := radius d
  let k := Real.sqrt (1 - d ^ 2)
  let x := z * (1 + (s : ℂ))
  have ha : 0 < a := radius_pos hd.le
  have hc : 0 < c := scale_pos hd
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 0 < 1 + s := by positivity
  have hx : x - (c : ℂ) ≠ 0 := by
    simpa [x, z, c] using near_sub_scale_ne hd hD hs1
  have hz : z - (c : ℂ) ≠ 0 := by
    simpa [z, c] using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  have heq : 1 + denominatorCoefficient d * (s : ℂ) = (x - (c : ℂ)) / (z - (c : ℂ)) := by
    change 1 + z / (z - (c : ℂ)) * (s : ℂ) = _
    field_simp [hz]
    simp only [x]
    ring
  have hzBound : ‖z - (c : ℂ)‖ ≤ a + c := by
    simpa [sub_eq_add_neg, norm_neg, norm_real, abs_of_pos hc, z, a, nearPoint_norm hd hD]
      using norm_add_le z (-(c : ℂ))
  have hratio : ‖z - (c : ℂ)‖ ≤ (2 * (n : ℝ)) * ‖x - (c : ℂ)‖ := by
    by_cases h : 1 / 2 ≤ d
    · have hca : a ≤ 3 * c := radius_le_three_scale hd hD h
      have hsk : c * k ≤ ‖x - (c : ℂ)‖ := by
        simpa only [x, z, c, k, ofReal_add, ofReal_one] using near_distance_sine hd hD (1 + s)
      calc
        _ ≤ 4 * c := hzBound.trans (by linarith)
        _ ≤ (2 * (n : ℝ)) * (c * k) := by
          nlinarith only [mul_le_mul_of_nonneg_left hS hc.le]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsk (by positivity)
    · have hca : c ≤ 2 * a := scale_le_two_radius hd hD
      have hk : (1 / 2 : ℝ) ≤ k := sine_ge_half hd (le_of_not_ge h)
      have him : (x - (c : ℂ)).im = a * k * (1 + s) := by
        simp only [x, sub_im, mul_im, add_im, one_im, ofReal_im, add_re, one_re,
          ofReal_re, add_zero, mul_zero, zero_add, sub_zero, z, a, k, near_im_radius hd]
      have hlow : a / 2 ≤ (x - (c : ℂ)).im := by
        rw [him]
        have hmul := mul_le_mul_of_nonneg_left hk ha.le
        have hmul' := mul_nonneg (mul_nonneg ha.le (Real.sqrt_nonneg (1 - d ^ 2))) hs
        nlinarith
      have hdNorm : a / 2 ≤ ‖x - (c : ℂ)‖ :=
        hlow.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
      calc
        _ ≤ 3 * a := hzBound.trans (by linarith)
        _ ≤ (2 * (n : ℝ)) * (a / 2) := by nlinarith [mul_nonneg ha.le (show 0 ≤ (n : ℝ) - 3 by linarith)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hdNorm (by positivity)
  rw [CutBounds.shortReciprocal, heq, inv_div, norm_mul, norm_inv, norm_div,
    show 1 + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; rfl, norm_real, Real.norm_eq_abs, abs_of_pos hs1]
  rw [mul_comm, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ hs1.le
  exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr hratio

/-- The local error envelope (5) for the actual near-ray amplitude. -/
theorem nearAmplitude_local_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8) :
    ‖nearAmplitude d s - 1‖ ≤ (2 * (n : ℝ) / 5 + 9) * s +
      (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2 := by
  rw [nearAmplitude_factorization hd hD hs]
  exact CutBounds.near_local_error hs hs₈ (denominator_near_bound hd hD).le le_rfl
    (rootRatios_majorants hd hD hS hL hs).2

/-- The pointwise bound for the near-ray amplitude on the entire outward ray. -/
theorem nearAmplitude_global {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) : ‖nearAmplitude d s‖ ≤ 2 * (n : ℝ) * (1 + (n : ℝ) * s / 8) := by
  rw [nearAmplitude_factorization hd hD hs, norm_mul]
  calc
    _ ≤ (2 * (n : ℝ) / (1 + s)) * ((1 + s) * (1 + (n : ℝ) * s / 8)) :=
      mul_le_mul (reciprocal_global hd hD hn hS hs) (rootRatios_majorants hd hD hS hL hs).1
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← mul_assoc, div_mul_cancel₀ _ (by positivity : (1 + s) ≠ 0)]

/-- The global error bound is contained in the common affine envelope of (6). -/
theorem nearAmplitude_tail_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) : ‖nearAmplitude d s - 1‖ ≤
      (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8) := by
  calc
    _ ≤ ‖nearAmplitude d s‖ + 1 := by simpa using norm_sub_le (nearAmplitude d s) 1
    _ ≤ 2 * (n : ℝ) * (1 + (n : ℝ) * s / 8) + 1 :=
      add_le_add_right (nearAmplitude_global hd hD hn hS hL hs) _
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hs]

/-- The nonzero endpoint by which the near prefactor is normalized. -/
theorem rayPrefactor_near_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    rayPrefactor d 0 (nearPoint d) ≠ 0 := by
  have hnc : nearPoint d - (scale d : ℂ) ≠ 0 := by
    simpa using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  rw [rayPrefactor_near_form]
  exact div_ne_zero (neg_ne_zero.mpr (otherRoots_ne hd hD))
    (mul_ne_zero (mul_ne_zero (by norm_num) (near_ne_zero hd hD))
      (sub_ne_zero.mpr (sub_ne_zero.mp hnc).symm))

private noncomputable def weightedNear (d : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s

/-- The normalized mean `J_n` of the actual near-ray amplitude. -/
noncomputable def nearMean (d : ℝ) (n : ℕ) : ℂ :=
  (∫ s in Ioi (0 : ℝ), weightedNear d n s) / (BetaMoments.mass n : ℂ)

private theorem rayIntegrand_near_eq {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (s : ℝ) :
    rayIntegrand d n 0 s = rayPrefactor d 0 (nearPoint d) * weightedNear d n s := by
  rw [rayIntegrand]
  change (Real.sqrt s : ℂ) * (1 + (s : ℂ))⁻¹ ^ (n + 1) *
      rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) = _
  simp only [weightedNear, BetaMoments.rayWeight, ofReal_div, ofReal_pow, ofReal_add, ofReal_one,
    nearAmplitude, inv_pow, div_eq_mul_inv, ofReal_mul, ofReal_inv]
  rw [show rayPrefactor d 0 (nearPoint d) *
      ((Real.sqrt s : ℂ) * ((1 + (s : ℂ)) ^ (n + 1))⁻¹ *
        (rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) *
          (rayPrefactor d 0 (nearPoint d))⁻¹)) =
      (Real.sqrt s : ℂ) * ((1 + (s : ℂ)) ^ (n + 1))⁻¹ *
        rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) *
        (rayPrefactor d 0 (nearPoint d) * (rayPrefactor d 0 (nearPoint d))⁻¹) by ring,
    mul_inv_cancel₀ (rayPrefactor_near_ne_zero hd hD), mul_one]

private theorem weightedNear_integrable {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) : IntegrableOn (weightedNear d n) (Ioi 0) := by
  have h := (rayIntegrand_integrable hd hD hn 0).const_mul (rayPrefactor d 0 (nearPoint d))⁻¹
  have hf : IntegrableOn (fun s => (rayPrefactor d 0 (nearPoint d))⁻¹ * rayIntegrand d n 0 s)
      (Ioi 0) := h
  refine hf.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [rayIntegrand_near_eq hd hD, ← mul_assoc, inv_mul_cancel₀ (rayPrefactor_near_ne_zero hd hD),
    one_mul]

/-- The near ray integral factors exactly into its endpoint, normalization,
and the mean of the amplitude whose error is estimated below. -/
theorem nearRay_integral_eq_mean {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    (∫ s in Ioi (0 : ℝ), rayIntegrand d n 0 s) =
      rayPrefactor d 0 (nearPoint d) * (BetaMoments.mass n : ℂ) * nearMean d n := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => rayIntegrand_near_eq hd hD n s),
    integral_const_mul, nearMean]
  have hb : (BetaMoments.mass n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (BetaMoments.mass_pos hn).ne'
  rw [mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hb]

private theorem rayWeight_integrable {n : ℕ} (hn : 0 < n) :
    IntegrableOn (BetaMoments.rayWeight n) (Ioi 0) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : (((0 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  simpa using BetaMoments.integrableOn_moment h

private theorem norm_weightedNear_sub_weight {d : ℝ} {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖ =
      ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s := by
  rw [weightedNear, show (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s -
      (BetaMoments.rayWeight n s : ℂ) =
    (BetaMoments.rayWeight n s : ℂ) * (nearAmplitude d s - 1) by ring,
    norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (BetaMoments.rayWeight_nonneg n hs),
    mul_comm]

private theorem weightedNear_loss_integrable {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) :
    IntegrableOn (fun s => ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) (Ioi 0) := by
  have hw : IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable hn).ofReal
  have h : IntegrableOn (fun s => ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖)
      (Ioi 0) := ((weightedNear_integrable hd hD hn).sub hw).norm
  exact h.congr_fun (fun _ hs => norm_weightedNear_sub_weight hs.le) measurableSet_Ioi

private theorem nearMean_norm_sub_one_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) :
    ‖nearMean d n - 1‖ ≤
      (∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) /
        BetaMoments.mass n := by
  have hpos := BetaMoments.mass_pos hn
  have hmass : (BetaMoments.mass n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have hcast : (∫ s in Ioi (0 : ℝ), (BetaMoments.rayWeight n s : ℂ)) =
      (BetaMoments.mass n : ℂ) := integral_complex_ofReal
  have hw : IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable hn).ofReal
  have hi := weightedNear_integrable hd hD hn
  unfold nearMean
  rw [div_sub_one hmass]
  have hdiff : (∫ s in Ioi (0 : ℝ), weightedNear d n s) - (BetaMoments.mass n : ℂ) =
      ∫ s in Ioi (0 : ℝ), (weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)) := by
    rw [integral_sub hi hw, hcast]
  rw [hdiff, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  have h := norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun s => weightedNear d n s - (BetaMoments.rayWeight n s : ℂ))
  have heq :
      (∫ s in Ioi (0 : ℝ), ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖) =
        ∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hs => norm_weightedNear_sub_weight hs.le)
  exact h.trans_eq heq

private theorem near_loss_integral_bound {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    (∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) /
      BetaMoments.mass n < 73 / 100 := by
  let M := BetaMoments.mass n
  let L : Set ℝ := Ioc 0 (1 / 8)
  let T : Set ℝ := Ioi (1 / 8)
  let f (s : ℝ) := ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s
  let g (s : ℝ) := ((2 * (n : ℝ) / 5 + 9) * s +
    (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * BetaMoments.rayWeight n s
  let h (s : ℝ) := ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) * BetaMoments.rayWeight n s
  have hnN : 0 < n := by omega
  have hM : 0 < M := BetaMoments.mass_pos hnN
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : 0 ≤ (1 / 8 : ℝ) := by norm_num
  have hf : IntegrableOn f (Ioi 0) := weightedNear_loss_integrable hd hD hnN
  have hfL : IntegrableOn f L := hf.mono_set Ioc_subset_Ioi_self
  have hfT : IntegrableOn f T := hf.mono_set (Ioi_subset_Ioi hR)
  have hLocalData := BetaMoments.near_local_integral_bound hn
  have hg : IntegrableOn g L := hLocalData.1
  have hhFull := (BetaMoments.affine_moment (n := n) (by linarith)
    (2 * (n : ℝ) + 1) ((2 * (n : ℝ) + 1) * (n : ℝ) / 8)).1
  have hh : IntegrableOn h T :=
    (hhFull.mono_set (Ioi_subset_Ioi hR)).congr_fun (fun s _ => by dsimp [h]; ring)
      measurableSet_Ioi
  have hcmpLocal : ∀ s ∈ L, f s ≤ g s := by
    intro s hs
    change s ∈ Ioc 0 (1 / 8) at hs
    exact mul_le_mul_of_nonneg_right (nearAmplitude_local_error hd hD hS hL hs.1.le hs.2)
      (BetaMoments.rayWeight_nonneg n hs.1.le)
  have hcmpTail : ∀ s ∈ T, f s ≤ h s := by
    intro s hs
    have hs0 : 0 ≤ s := hR.trans (mem_Ioi.mp hs).le
    exact mul_le_mul_of_nonneg_right (nearAmplitude_tail_error hd hD hn hS hL hs0)
      (BetaMoments.rayWeight_nonneg n hs0)
  have hLocalLe : (∫ s in L, f s) ≤ ∫ s in L, g s :=
    setIntegral_mono_on hfL hg measurableSet_Ioc hcmpLocal
  have hTailLe : (∫ s in T, f s) ≤ ∫ s in T, h s :=
    setIntegral_mono_on hfT hh measurableSet_Ioi hcmpTail
  have hLocal : (∫ s in L, f s) / M < 71 / 100 :=
    (div_le_div_of_nonneg_right hLocalLe hM.le).trans_lt hLocalData.2
  have hTail : (∫ s in T, f s) / M < 1 / 50 :=
    (div_le_div_of_nonneg_right hTailLe hM.le).trans_lt (BetaMoments.near_tail_integral_bound hn)
  have hdisj : Disjoint L T := Set.disjoint_left.mpr fun _ hs ht => (not_lt_of_ge hs.2) ht
  have hunion : L ∪ T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hR
  have hsplit : (∫ s in Ioi (0 : ℝ), f s) = (∫ s in L, f s) + ∫ s in T, f s := by
    calc
      _ = ∫ s in L ∪ T, f s := by rw [hunion]
      _ = _ := setIntegral_union hdisj measurableSet_Ioi hfL hfT
  change (∫ s in Ioi (0 : ℝ), f s) / M < _
  rw [hsplit, add_div]
  exact (add_lt_add hLocal hTail).trans_le (by norm_num)

/-- The checked near-ray mean lies within `73/100` of one in the interior
range where both radial endpoint distances have the indicated lower bounds. -/
theorem nearMean_close_to_one {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    ‖nearMean d n - 1‖ < 73 / 100 :=
  (nearMean_norm_sub_one_le hd hD (by omega)).trans_lt (near_loss_integral_bound hd hD hn hS hL)

private theorem weightedNear_succ (d : ℝ) (n : ℕ) (s : ℝ) :
    weightedNear d (n + 1) s = weightedNear d n s * ((1 + s)⁻¹ : ℝ) := by
  unfold weightedNear
  have h := BetaMoments.rayWeight_shift (Nat.le_succ n) s
  rw [show n.succ - n = 1 by omega, pow_one] at h
  rw [h, ofReal_mul]
  ring

/-- The covariance of the actual near-ray amplitude with the one-step tilt.
The second factor is centered at its checked mean, as in (8). -/
noncomputable def nearTiltCovariance (d : ℝ) (n : ℕ) : ℂ :=
  (∫ s in Ioi (0 : ℝ), weightedNear d n s *
      (((1 + s)⁻¹ - ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) : ℝ) : ℂ)) /
    (BetaMoments.mass n : ℂ)

/-- The exact step identity (8) for the actual near-ray amplitude. -/
theorem nearMean_step_covariance {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    nearMean d (n + 1) - nearMean d n =
      nearTiltCovariance d n / ((((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  let ηR := ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1)
  let η : ℂ := (ηR : ℂ)
  let M : ℂ := (BetaMoments.mass n : ℂ)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hηR : 0 < ηR := div_pos (by linarith) (by positivity)
  have hη : η ≠ 0 := ofReal_ne_zero.mpr hηR.ne'
  have hM : M ≠ 0 := ofReal_ne_zero.mpr (BetaMoments.mass_pos hn).ne'
  have ht : (fun s : ℝ => weightedNear d n s * (((1 + s)⁻¹ - ηR : ℝ) : ℂ)) =
      (fun s : ℝ => weightedNear d (n + 1) s - η * weightedNear d n s) := by
    ext s
    rw [weightedNear_succ, ofReal_sub]
    change weightedNear d n s * (((1 + s)⁻¹ : ℝ) - η) =
      weightedNear d n s * ((1 + s)⁻¹ : ℝ) - η * weightedNear d n s
    ring
  have h₀ := weightedNear_integrable hd hD hn
  have h₁ := weightedNear_integrable hd hD (Nat.succ_pos n)
  unfold nearMean nearTiltCovariance
  rw [BetaMoments.mass_succ hn, ofReal_mul]
  change (∫ s in Ioi (0 : ℝ), weightedNear d (n + 1) s) / (η * M) -
      (∫ s in Ioi (0 : ℝ), weightedNear d n s) / M =
    (∫ s in Ioi (0 : ℝ), weightedNear d n s * (((1 + s)⁻¹ - ηR : ℝ) : ℂ)) / M / η
  rw [ht, integral_sub h₁ (h₀.const_mul η), integral_const_mul]
  field_simp [hη, hM]
  ring

private theorem rayWeight_succ_complex (n : ℕ) (s : ℝ) :
    (BetaMoments.rayWeight (n + 1) s : ℂ) =
      (BetaMoments.rayWeight n s : ℂ) * ((1 + s)⁻¹ : ℝ) := by
  have h := BetaMoments.rayWeight_shift (Nat.le_succ n) s
  rw [show n.succ - n = 1 by omega, pow_one] at h
  exact_mod_cast h

/-- Subtracting a constant from the amplitude leaves the covariance unchanged.
Use the near mean to recover the usual doubly centered covariance, or one
to estimate the loss from the constant term. -/
theorem nearTiltCovariance_sub_const {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 0 < n) (a : ℂ) :
    nearTiltCovariance d n =
      (∫ s in Ioi (0 : ℝ), (BetaMoments.rayWeight n s : ℂ) * (nearAmplitude d s - a) *
        (((1 + s)⁻¹ - ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) : ℝ) : ℂ)) /
        (BetaMoments.mass n : ℂ) := by
  let ηR := ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1)
  let η : ℂ := (ηR : ℂ)
  let g (s : ℝ) : ℂ := weightedNear d n s * (((1 + s)⁻¹ - ηR : ℝ) : ℂ)
  let v (s : ℝ) : ℂ := (BetaMoments.rayWeight n s : ℂ) * (((1 + s)⁻¹ - ηR : ℝ) : ℂ)
  have hgEq : g = fun s => weightedNear d (n + 1) s - η * weightedNear d n s := by
    funext s
    dsimp only [g]
    rw [weightedNear_succ, ofReal_sub]
    dsimp only [η]
    ring
  have hvEq : v = fun s => (BetaMoments.rayWeight (n + 1) s : ℂ) -
      η * (BetaMoments.rayWeight n s : ℂ) := by
    funext s
    dsimp only [v]
    rw [rayWeight_succ_complex, ofReal_sub]
    dsimp only [η]
    ring
  have h0 := weightedNear_integrable hd hD hn
  have h1 := weightedNear_integrable hd hD (Nat.succ_pos n)
  have hw0 : IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable hn).ofReal
  have hw1 : IntegrableOn (fun s => (BetaMoments.rayWeight (n + 1) s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable (Nat.succ_pos n)).ofReal
  have hg : IntegrableOn g (Ioi 0) := hgEq ▸ h1.sub (h0.const_mul η)
  have hv : IntegrableOn v (Ioi 0) := hvEq ▸ hw1.sub (hw0.const_mul η)
  have hvInt : (∫ s in Ioi (0 : ℝ), v s) = 0 := by
    rw [hvEq, integral_sub hw1 (hw0.const_mul η), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, ← BetaMoments.mass, ← BetaMoments.mass,
      BetaMoments.mass_succ hn, ofReal_mul]
    exact sub_self _
  have hpoint (s : ℝ) : (BetaMoments.rayWeight n s : ℂ) * (nearAmplitude d s - a) *
      (((1 + s)⁻¹ - ηR : ℝ) : ℂ) = g s - a * v s := by
    dsimp only [g, v, weightedNear]
    ring
  change (∫ s in Ioi (0 : ℝ), g s) / (BetaMoments.mass n : ℂ) =
    (∫ s in Ioi (0 : ℝ), (BetaMoments.rayWeight n s : ℂ) * (nearAmplitude d s - a) *
      (((1 + s)⁻¹ - ηR : ℝ) : ℂ)) / (BetaMoments.mass n : ℂ)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpoint s),
    integral_sub hg (hv.const_mul a), integral_const_mul, hvInt, mul_zero, sub_zero]

end CatalanStrictPeaks.CutGeometry
