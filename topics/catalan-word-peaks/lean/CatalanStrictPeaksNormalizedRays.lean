import CatalanStrictPeaksFarRay
import Mathlib.Data.Fin.Rev

/-!
# Real normalization of the four-ray Catalan coefficient

The radial integrands at conjugate cuts are exact complex conjugates.
The resulting real decomposition uses the established near mean and far error.
-/

namespace CatalanStrictPeaks.CutGeometry

open Complex MeasureTheory Set
open scoped ComplexConjugate

private theorem cutPoint_rev (d : ℝ) (j : Fin 4) : cutPoint d j.rev = conj (cutPoint d j) := by
  fin_cases j <;> simp [cutPoint, Fin.rev]

private theorem cutPoint_pos_scale_ne {d a b : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : Fin 4} (hij : i ≠ j) (ha : 0 < a) (hb : 0 < b) :
    cutPoint d j * (a : ℂ) ≠ cutPoint d i * (b : ℂ) := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hre him
  have hs (r : ℝ) (hr : 0 < r) :
      0 < (nearPoint d).re * r ∧ (farPoint d).re * r < 0 ∧
      0 < (nearPoint d).im * r ∧ 0 < (farPoint d).im * r :=
    ⟨mul_pos (nearPoint_re_pos hd) hr, mul_neg_of_neg_of_pos (farPoint_re_neg hd) hr,
      mul_pos (nearPoint_im_pos hd hD) hr, mul_pos (farPoint_im_pos hd hD) hr⟩
  obtain ⟨ha₁, ha₂, ha₃, ha₄⟩ := hs a ha
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hs b hb
  fin_cases i <;> fin_cases j <;>
    simp only [cutPoint, Complex.conj_re, Complex.conj_im, neg_mul] at hre him <;>
    first | exact hij rfl | linarith

private theorem cutPoint_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    cutPoint d i ≠ 0 := by
  have hz := nearPoint_im_pos hd hD
  have hw := farPoint_im_pos hd hD
  intro hz'
  have hi := congrArg Complex.im hz'
  fin_cases i <;> simp [cutPoint] at hi <;> linarith

private theorem cutFactor_argument_ne_pi {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : Fin 4} (hij : i ≠ j) (ht : 0 < t) :
    (1 - (cutPoint d j * (t : ℂ)) / cutPoint d i).arg ≠ Real.pi := by
  let q := (cutPoint d j * (t : ℂ)) / cutPoint d i
  intro ha
  change (1 - q).arg = Real.pi at ha
  obtain ⟨hr, hi⟩ := Complex.arg_eq_pi_iff.1 ha
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hr hi
  have hq : q = (q.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      linarith
  have he := (div_eq_iff (cutPoint_ne_zero hd hD i)).mp hq
  exact cutPoint_pos_scale_ne hd hD hij ht (show 0 < q.re by linarith)
    (by simpa only [mul_comm] using he)

private theorem cutFactor_conj {z x : ℂ} (h : (1 - x / z).arg ≠ Real.pi) :
    cutFactor (conj z) (conj x) = conj (cutFactor z x) := by
  simp only [cutFactor, principalRoot]
  rw [show 1 - conj x / conj z = conj (1 - x / z) by simp, Complex.conj_cpow _ _ h]
  rw [map_ofNat]

private theorem rayPrefactor_rev {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (ht : 0 < t) :
    rayPrefactor d j.rev (conj (cutPoint d j * (t : ℂ))) =
      conj (rayPrefactor d j (cutPoint d j * (t : ℂ))) := by
  let x := cutPoint d j * (t : ℂ)
  have hmem {i k : Fin 4} (hi : i ∈ Finset.univ.erase k) :
      i.rev ∈ Finset.univ.erase k.rev :=
    Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hi).1 (Fin.rev_injective h),
      Finset.mem_univ _⟩
  have hprod :
      (∏ i ∈ Finset.univ.erase j, conj (cutFactor (cutPoint d i) x)) =
      ∏ i ∈ Finset.univ.erase j.rev, cutFactor (cutPoint d i) (conj x) := by
    refine Finset.prod_bij' (fun i _ => i.rev) (fun i _ => i.rev)
      (fun i hi => hmem hi) (fun i hi => by simpa using hmem hi)
      (fun i _ => Fin.rev_rev i) (fun i _ => Fin.rev_rev i) ?_
    intro i hi
    rw [cutPoint_rev]
    exact (cutFactor_conj (cutFactor_argument_ne_pi hd hD (Finset.mem_erase.mp hi).1 ht)).symm
  change rayPrefactor d j.rev (conj x) = conj (rayPrefactor d j x)
  simp only [rayPrefactor, map_div₀, map_neg, map_mul, map_sub, map_ofNat, Complex.conj_ofReal,
    map_prod, hprod]

private theorem rayIntegrand_rev {d s : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (hs : 0 < s) :
    rayIntegrand d n j.rev s = conj (rayIntegrand d n j s) := by
  have h := rayPrefactor_rev hd hD j (show 0 < 1 + s by positivity)
  rw [Complex.ofReal_add, Complex.ofReal_one] at h
  simp only [map_mul, map_add, map_one, Complex.conj_ofReal, ← cutPoint_rev d j] at h
  simp only [rayIntegrand, map_mul, map_pow, map_inv₀, map_add, map_one, Complex.conj_ofReal]
  rw [h]

/-- The coefficient terms from opposite cuts are exact complex conjugates. -/
theorem rayCoefficientTerm_rev {d : ℝ} (hd : 0 < d) (hD : d < 1) (n : ℕ) (j : Fin 4) :
    rayCoefficientTerm d n j.rev = conj (rayCoefficientTerm d n j) := by
  rw [rayCoefficientTerm, rayCoefficientTerm,
    setIntegral_congr_fun measurableSet_Ioi (fun _ hs => rayIntegrand_rev hd hD n j hs),
    integral_conj, cutPoint_rev]
  simp

/-- The unit-modulus phase factor carried by the upper near ray. -/
noncomputable def nearPhaseUnit (d : ℝ) (n : ℕ) : ℂ :=
  -(nearPoint d)⁻¹ ^ n * rayPrefactor d 0 (nearPoint d) /
    (((radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖ : ℝ) : ℂ)

theorem norm_nearPhaseUnit {d : ℝ} (hd : 0 < d) (hD : d < 1) (n : ℕ) :
    ‖nearPhaseUnit d n‖ = 1 := by
  have h : 0 < (radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖ :=
    mul_pos (pow_pos (inv_pos.2 (radius_pos hd.le)) _) (norm_pos_iff.mpr (rayPrefactor_near_ne_zero hd hD))
  rw [nearPhaseUnit, norm_div, norm_mul, norm_neg, norm_pow, norm_inv,
    nearPoint_norm hd hD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h, div_self h.ne']

/-- The actual polynomial value in the units of the leading near amplitude. -/
noncomputable def normalizedCoefficient (d : ℝ) (n : ℕ) : ℝ :=
  scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) / rayLeadingScale d n

private theorem nearCoefficientTerm_normalization {d : ℝ} {n : ℕ} (hd : 0 < d)
    (hD : d < 1) (hn : 0 < n) :
    2 * (rayCoefficientTerm d n 0).re / rayLeadingScale d n =
      (nearPhaseUnit d n * nearMean d n).re := by
  let A := (radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖
  have hA : 0 < A := mul_pos (pow_pos (inv_pos.2 (radius_pos hd.le)) _)
    (norm_pos_iff.mpr (rayPrefactor_near_ne_zero hd hD))
  have hscale : rayLeadingScale d n = (2 / Real.pi) * BetaMoments.mass n * A := by
    dsimp [rayLeadingScale, A]
    ring
  have hreal : (2 : ℂ) * rayCoefficientTerm d n 0 =
      (rayLeadingScale d n : ℂ) * (nearPhaseUnit d n * nearMean d n) := by
    rw [rayCoefficientTerm, nearRay_integral_eq_mean hd hD hn, nearPhaseUnit, hscale]
    change (2 : ℂ) * ((-((nearPoint d)⁻¹ ^ n) / (Real.pi : ℂ)) * _) =
      (((2 / Real.pi) * BetaMoments.mass n * A : ℝ) : ℂ) *
        (-(nearPoint d)⁻¹ ^ n * rayPrefactor d 0 (nearPoint d) / (A : ℂ) * nearMean d n)
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hA.ne']
    ring
  have hre := congrArg Complex.re hreal
  have hre2 : (2 : ℂ).re = 2 := by norm_num
  have him2 : (2 : ℂ).im = 0 := by norm_num
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2, him2,
    zero_mul, sub_zero] at hre
  exact (div_eq_iff (rayLeadingScale_pos hd hD hn).ne').2 (hre.trans (mul_comm _ _))

/-- The exact normalized coefficient as a near-ray mean and a real far-ray error. -/
theorem normalizedCoefficient_eq_near_add_far {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    normalizedCoefficient d n = (nearPhaseUnit d n * nearMean d n).re + farRayError d n := by
  have h := analyticGenerating_fourRays hd hD hn
  change _ = ∑ j : Fin 4, rayCoefficientTerm d n j at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  have hr := congrArg Complex.re h
  change scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) =
      (rayCoefficientTerm d n 0 + (rayCoefficientTerm d n 1 +
        (rayCoefficientTerm d n 2 + rayCoefficientTerm d n 3))).re at hr
  have hconj : rayCoefficientTerm d n 3 = conj (rayCoefficientTerm d n 0) :=
    rayCoefficientTerm_rev hd hD n 0
  rw [hconj] at hr
  have hp : scale d ^ n * (C n).eval (1 - (scale d ^ 2)⁻¹) =
      2 * (rayCoefficientTerm d n 0).re +
      (rayCoefficientTerm d n 1 + rayCoefficientTerm d n 2).re := by
    simp only [Complex.add_re, Complex.conj_re] at hr ⊢
    linarith
  rw [normalizedCoefficient, hp, add_div, nearCoefficientTerm_normalization hd hD hn, farRayError]

/-- In the interior band the actual normalized value is within 77/100 of
the real part of its leading phase. -/
theorem normalizedCoefficient_close_to_phase {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    |normalizedCoefficient d n - (nearPhaseUnit d n).re| < 77 / 100 := by
  have hn0 : 0 < n := by omega
  have hnr := nearMean_close_to_one hd hD hn hsin (by linarith : 2 ≤ (n : ℝ) * d)
  have hfar := farRayError_interior hd hD hn hnd hsin
  have hne :
      |(nearPhaseUnit d n * nearMean d n).re - (nearPhaseUnit d n).re| < 73 / 100 := by
    rw [← Complex.sub_re, show nearPhaseUnit d n * nearMean d n - nearPhaseUnit d n =
      nearPhaseUnit d n * (nearMean d n - 1) by ring]
    exact (Complex.abs_re_le_norm _).trans_lt (by
      simpa only [norm_mul, norm_nearPhaseUnit hd hD n, one_mul] using hnr)
  rw [normalizedCoefficient_eq_near_add_far hd hD hn0,
    show (nearPhaseUnit d n * nearMean d n).re + farRayError d n - (nearPhaseUnit d n).re =
      ((nearPhaseUnit d n * nearMean d n).re - (nearPhaseUnit d n).re) + farRayError d n by ring]
  exact (abs_add_le _ _).trans_lt (by linarith)

/-- The original polynomial has the alternating sign at each phase level
where the quantitative interior premises hold. -/
theorem eval_sign_of_nearPhaseUnit {d : ℝ} {n k : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2))
    (hphase : (nearPhaseUnit d n).re = (-1 : ℝ) ^ k) :
    0 < (-1 : ℝ) ^ k * (C n).eval (1 - (scale d ^ 2)⁻¹) := by
  have hn0 : 0 < n := by omega
  have hb := normalizedCoefficient_close_to_phase hd hD hn hnd hsin
  rw [hphase] at hb
  let e := (-1 : ℝ) ^ k
  have he : |e| = 1 := by simp [e, abs_pow]
  have he2 : e ^ 2 = 1 := by dsimp [e]; rw [pow_right_comm]; norm_num
  have he' : |e * (normalizedCoefficient d n - e)| < 77 / 100 := by
    rw [abs_mul, he, one_mul]
    exact hb
  have hY : 0 < e * normalizedCoefficient d n := by
    have hm := (abs_lt.mp he').1
    rw [mul_sub, ← pow_two, he2] at hm
    linarith
  rw [normalizedCoefficient, ← mul_div_assoc, ← mul_left_comm] at hY
  exact (pos_of_mul_pos_right
    ((div_pos_iff_of_pos_right (rayLeadingScale_pos hd hD hn0)).mp hY)
    (pow_nonneg (scale_pos hd).le _))

end CatalanStrictPeaks.CutGeometry
