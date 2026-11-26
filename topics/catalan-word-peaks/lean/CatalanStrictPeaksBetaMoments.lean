import CatalanStrictPeaksMomentArithmetic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integral moments for the Catalan radial density

The substitution `s = x⁻¹ - 1` identifies the actual improper integral
with the beta integral on the unit interval.
-/

namespace CatalanStrictPeaks.BetaMoments

open Set MeasureTheory Function
open scoped BigOperators

private noncomputable def betaPrime (a b s : ℝ) : ℝ :=
  s ^ (a - 1) / (1 + s) ^ (a + b)

private noncomputable def betaKernel (a b x : ℝ) : ℝ :=
  x ^ (a - 1) * (1 - x) ^ (b - 1)

private noncomputable def toRay (x : ℝ) : ℝ := x⁻¹ - 1

private theorem toRay_image : toRay '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sub_pos.mpr ((one_lt_inv₀ hx.1).mpr hx.2)
  · intro hs
    have hs' : 0 < s := hs
    have h : 1 < 1 + s := by linarith
    refine ⟨(1 + s)⁻¹, ⟨by positivity, inv_lt_one_of_one_lt₀ h⟩, ?_⟩
    simp [toRay]

private theorem toRay_inj : InjOn toRay (Ioo (0 : ℝ) 1) := by
  intro x _ y _ h
  exact inv_injective (sub_left_inj.mp h)

private theorem toRay_deriv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt toRay (-(x ^ 2)⁻¹) (Ioo 0 1) x :=
  ((hasDerivAt_inv hx.1.ne').sub_const 1).hasDerivWithinAt

private theorem betaPrime_pullback (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |-(x ^ 2)⁻¹| • betaPrime a b (toRay x) = betaKernel b a x := by
  have hx' : 0 < x := hx.1
  have hleft : 0 ≤ 1 - x := by linarith [hx.2]
  have hsum : 1 + toRay x = x⁻¹ := by unfold toRay; ring
  have hray : toRay x = (1 - x) / x := by
    unfold toRay
    field_simp [hx'.ne']
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (x ^ 2)⁻¹),
    betaPrime, betaKernel, hsum, hray, Real.div_rpow hleft hx'.le,
    Real.inv_rpow hx'.le, div_inv_eq_mul, ← Real.rpow_natCast x 2,
    ← Real.rpow_neg hx'.le, div_eq_mul_inv, ← Real.rpow_neg hx'.le]
  calc
    _ = (1 - x) ^ (a - 1) * ((x ^ (-(2 : ℝ)) * x ^ (-(a - 1))) * x ^ (a + b)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_add hx', ← Real.rpow_add hx',
        show -(2 : ℝ) + (-(a - 1)) + (a + b) = b - 1 by ring]
      ring

private theorem betaKernel_cast (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (betaKernel a b x : ℂ) =
      (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
  rw [betaKernel, Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
  push_cast
  rfl

private theorem betaKernel_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaKernel a b) (Ioo 0 1) := by
  have hc := Complex.betaIntegral_convergent
    (u := (a : ℂ)) (v := (b : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hc
  have hr : IntegrableOn
      (fun x : ℝ => (((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) : ℂ).re)
      (Ioo 0 1) := hc.re
  refine hr.congr_fun (fun x hx => ?_) measurableSet_Ioo
  simpa only [Complex.ofReal_re] using congrArg Complex.re (betaKernel_cast a b x hx).symm

private theorem betaPrime_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaPrime a b) (Ioi 0) := by
  rw [← toRay_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo toRay_deriv toRay_inj]
  exact (betaKernel_integrable hb ha).congr_fun
    (fun x hx => (betaPrime_pullback a b x hx).symm) measurableSet_Ioo

private theorem betaKernel_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioo (0 : ℝ) 1, betaKernel a b x) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_div, Complex.ofReal_mul,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, Complex.ofReal_add]
  have hB : (∫ x in Ioo (0 : ℝ) 1, (betaKernel a b x : ℂ)) =
      Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo (betaKernel_cast a b)
  rw [hB]
  have ha' : 0 < ((a : ℂ)).re := by simpa
  have hb' : 0 < ((b : ℂ)).re := by simpa
  have hab : 0 < ((a : ℂ) + (b : ℂ)).re := by simpa using add_pos ha hb
  apply (eq_div_iff (Complex.Gamma_ne_zero_of_re_pos hab)).2
  rw [mul_comm]
  exact (Complex.Gamma_mul_Gamma_eq_betaIntegral ha' hb').symm

private theorem betaPrime_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s in Ioi (0 : ℝ), betaPrime a b s) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  rw [← toRay_image, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo toRay_deriv toRay_inj]
  rw [setIntegral_congr_fun measurableSet_Ioo (betaPrime_pullback a b)]
  rw [betaKernel_integral hb ha, mul_comm, add_comm]

/-- The unnormalized density of the radial displacement at length `n`. -/
noncomputable def rayWeight (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt s / (1 + s) ^ (n + 1)

/-- The normalizing integral `b(n)` in the Catalan proof. -/
noncomputable def mass (n : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), rayWeight n s

/-- The integral of the displacement to power `j` against the unnormalized density. -/
noncomputable def rawMoment (n j : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ j * rayWeight n s

/-- The normalized moment `M_j` used in the Catalan proof. -/
noncomputable def moment (n j : ℕ) : ℝ := rawMoment n j / mass n

private theorem moment_kernel (n j : ℕ) {s : ℝ} (hs : 0 < s) :
    s ^ j * rayWeight n s = betaPrime ((j : ℝ) + 3 / 2) ((n : ℝ) - j - 1 / 2) s := by
  rw [rayWeight, betaPrime, Real.sqrt_eq_rpow, ← mul_div_assoc,
    ← Real.rpow_natCast s j, ← Real.rpow_add hs, ← Real.rpow_natCast (1 + s) (n + 1)]
  push_cast
  congr 2 <;> ring

/-- The moment integrals converge in the parameter range used here. -/
theorem integrableOn_moment {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    IntegrableOn (fun s : ℝ => s ^ j * rayWeight n s) (Ioi 0) := by
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 1 / 2 := by linarith
  exact (betaPrime_integrable ha hb).congr_fun
    (fun _ hs => (moment_kernel n j hs).symm) measurableSet_Ioi

/-- The improper integral appearing in the ray calculation is a beta moment. -/
theorem rawMoment_gamma {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    rawMoment n j =
      Real.Gamma ((j : ℝ) + 3 / 2) * Real.Gamma ((n : ℝ) - j - 1 / 2) /
        Real.Gamma ((n : ℝ) + 1) := by
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 1 / 2 := by linarith
  rw [rawMoment, setIntegral_congr_fun measurableSet_Ioi (fun _ hs => moment_kernel n j hs),
    betaPrime_integral ha hb]
  congr 2
  ring

private theorem rawMoment_zero (n : ℕ) : rawMoment n 0 = mass n := by
  simp [rawMoment, mass]

private theorem mass_gamma {n : ℕ} (hn : 0 < n) :
    mass n = Real.Gamma (3 / 2) * Real.Gamma ((n : ℝ) - 1 / 2) /
      Real.Gamma ((n : ℝ) + 1) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : ((0 : ℕ) : ℝ) + 1 / 2 < (n : ℝ) := by simp only [Nat.cast_zero]; linarith
  simpa [rawMoment_zero] using rawMoment_gamma h

/-- The normalizing integral is strictly positive for every positive length. -/
theorem mass_pos {n : ℕ} (hn : 0 < n) : 0 < mass n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [mass_gamma hn]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
    (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by positivity))

/-- Increasing the length tilts the density by the reciprocal of `1+s`. -/
theorem mass_succ {n : ℕ} (hn : 0 < n) :
    mass (n + 1) = ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) * mass n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hb : 0 < (n : ℝ) + 1 := by positivity
  rw [mass_gamma (Nat.succ_pos n), mass_gamma hn, Nat.cast_succ,
    show (n : ℝ) + 1 - 1 / 2 = ((n : ℝ) - 1 / 2) + 1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne']
  field_simp [hb.ne', (Real.Gamma_pos_of_pos hb).ne']
  ring

/-- Recurrence for the normalized moments with finite next moment. -/
theorem moment_succ {n j : ℕ} (h : (j : ℝ) + 3 / 2 < (n : ℝ)) :
    moment n (j + 1) =
      ((j : ℝ) + 3 / 2) / ((n : ℝ) - j - 3 / 2) * moment n j := by
  have hs : (((j + 1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by push_cast; linarith
  have hbase : (j : ℝ) + 1 / 2 < (n : ℝ) := by linarith
  have ha : 0 < (j : ℝ) + 3 / 2 := by positivity
  have hb : 0 < (n : ℝ) - j - 3 / 2 := by linarith
  rw [moment, moment, rawMoment_gamma hs, rawMoment_gamma hbase, Nat.cast_add, Nat.cast_one,
    show (j : ℝ) + 1 + 3 / 2 = ((j : ℝ) + 3 / 2) + 1 by ring,
    show (n : ℝ) - ((j : ℝ) + 1) - 1 / 2 = (n : ℝ) - j - 3 / 2 by ring,
    show (n : ℝ) - j - 1 / 2 = ((n : ℝ) - j - 3 / 2) + 1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne']
  let a := (j : ℝ) + 3 / 2
  let b := (n : ℝ) - j - 3 / 2
  change (a * Real.Gamma a) * Real.Gamma b / Real.Gamma ((n : ℝ) + 1) / mass n =
    a / b * (Real.Gamma a * (b * Real.Gamma b) / Real.Gamma ((n : ℝ) + 1) / mass n)
  rw [show Real.Gamma a * (b * Real.Gamma b) / Real.Gamma ((n : ℝ) + 1) / mass n =
      b * (Real.Gamma a * Real.Gamma b / Real.Gamma ((n : ℝ) + 1) / mass n) by ring,
    ← mul_assoc, div_mul_cancel₀ a hb.ne']
  ring

/-- All normalized moments with `j + 1/2 < n`, in the product form used in the proof. -/
theorem moment_product {n j : ℕ} (h : (j : ℝ) + 1 / 2 < (n : ℝ)) :
    moment n j =
      ∏ k ∈ Finset.range j, (((k : ℝ) + 3 / 2) / ((n : ℝ) - k - 3 / 2)) := by
  induction j with
  | zero =>
    have hn' : (0 : ℝ) < (n : ℝ) := by simp only [Nat.cast_zero] at h; linarith
    have hn : 0 < n := by exact_mod_cast hn'
    simp [moment, rawMoment_zero, (mass_pos hn).ne']
  | succ j ih =>
    have hs : (j : ℝ) + 3 / 2 < (n : ℝ) := by push_cast at h; linarith
    rw [moment_succ hs, Finset.prod_range_succ, ih (by linarith), mul_comm]

/-- The first normalized displacement moment. -/
theorem moment_one {n : ℕ} (hn : (3 / 2 : ℝ) < (n : ℝ)) :
    moment n 1 = (3 / 2) / ((n : ℝ) - 3 / 2) := by
  have h : ((1 : ℕ) : ℝ) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  rw [moment_product h]
  norm_num [Finset.prod_range_succ]

/-- The second normalized displacement moment. -/
theorem moment_two {n : ℕ} (hn : (5 / 2 : ℝ) < (n : ℝ)) :
    moment n 2 =
      (15 / 4) / (((n : ℝ) - 3 / 2) * ((n : ℝ) - 5 / 2)) := by
  have h : ((1 : ℕ) : ℝ) + 3 / 2 < (n : ℝ) := by norm_num; linarith
  change moment n (1 + 1) = _
  rw [moment_succ h, moment_one (by linarith), Nat.cast_one,
    show (n : ℝ) - 1 - 3 / 2 = (n : ℝ) - 5 / 2 by ring, div_mul_div_comm]
  rw [mul_comm ((n : ℝ) - 5 / 2)]
  norm_num

/-- The variance of radial displacement in the Catalan ray density. -/
theorem variance_formula {n : ℕ} (hn : (5 / 2 : ℝ) < (n : ℝ)) :
    moment n 2 - moment n 1 ^ 2 =
      (3 / 2) * n / (((n : ℝ) - 3 / 2) ^ 2 * ((n : ℝ) - 5 / 2)) := by
  rw [moment_one (by linarith), moment_two hn]
  set a := (n : ℝ) - 3 / 2
  set b := (n : ℝ) - 5 / 2
  have h₁ : 0 < a := by dsimp [a]; linarith
  have h₂ : 0 < b := by dsimp [b]; linarith
  field_simp [h₁.ne', h₂.ne']
  dsimp [a, b]
  ring

/-- Changing the size multiplies the unnormalized density by a power of
`(1+s)⁻¹`, the tilt factor used in the moment and tail arguments. -/
theorem rayWeight_shift {N n : ℕ} (h : N ≤ n) (s : ℝ) :
    rayWeight n s = rayWeight N s * ((1 + s)⁻¹) ^ (n - N) := by
  rw [rayWeight, rayWeight, inv_pow, ← div_eq_mul_inv, div_div, ← pow_add,
    show N + 1 + (n - N) = n + 1 by omega]

/-- The expectation of the one-step tilt factor, as in (8). -/
theorem tilt_mean {n : ℕ} (hn : 0 < n) :
    (∫ s in Ioi (0 : ℝ), (1 + s)⁻¹ * rayWeight n s) / mass n =
      ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) := by
  have hd (s : ℝ) : (1 + s)⁻¹ * rayWeight n s = rayWeight (n + 1) s := by
    rw [rayWeight_shift (Nat.le_succ n), show n.succ - n = 1 by omega, pow_one, mul_comm]
  simp_rw [hd]
  rw [← mass, mass_succ hn, mul_div_cancel_right₀ _ (mass_pos hn).ne']

private theorem scaledMass_monotone :
    Monotone (fun n : ℕ => (n : ℝ) ^ 2 * mass n) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using (mass_pos (n := 1) (by decide)).le
  · have hnN : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    apply sub_nonneg.mp
    change 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * mass (n + 1)) - ((n : ℝ) ^ 2 * mass n)
    rw [mass_succ hnN, Nat.cast_add, Nat.cast_one,
      show ((n : ℝ) + 1) ^ 2 * (((n : ℝ) - 1 / 2) / ((n : ℝ) + 1) * mass n) -
          (n : ℝ) ^ 2 * mass n = (((n : ℝ) - 1) / 2) * mass n by
        have hnp : 0 < (n : ℝ) + 1 := by positivity
        field_simp [hnp.ne']
        ring]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hnR) (by norm_num)) (mass_pos hnN).le

/-- A ratio bound for the normalizations. It follows directly from the exact
tilt recurrence, without asymptotics for the beta function. -/
theorem mass_ratio_le {N n : ℕ} (hN : 0 < N) (hNn : N ≤ n) :
    mass N / mass n ≤ ((n : ℝ) / (N : ℝ)) ^ 2 := by
  have hn : 0 < n := hN.trans_le hNn
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNpow : 0 < (N : ℝ) ^ 2 := pow_pos hNr 2
  rw [div_pow]
  apply (div_le_div_iff₀ (mass_pos hn) hNpow).2
  simpa only [mul_comm] using scaledMass_monotone hNn

private theorem rayWeight_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ rayWeight n s := by
  unfold rayWeight
  positivity

private theorem affine_moment {n : ℕ} (hn : (3 / 2 : ℝ) < (n : ℝ)) (A B : ℝ) :
    IntegrableOn (fun s => (A + B * s) * rayWeight n s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight n s) =
        mass n * (A + B * moment n 1) := by
  have h₀ : (((0 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have h₁ : (((1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hnNat : 0 < n := by exact_mod_cast hnR
  have hw₀ : IntegrableOn (rayWeight n) (Ioi 0) := by
    simpa using integrableOn_moment h₀
  have hw₁ : IntegrableOn (fun s => s * rayWeight n s) (Ioi 0) := by
    simpa using integrableOn_moment h₁
  have hA : IntegrableOn (fun s => A * rayWeight n s) (Ioi 0) := hw₀.const_mul A
  have hB : IntegrableOn (fun s => B * (s * rayWeight n s)) (Ioi 0) := hw₁.const_mul B
  simp_rw [add_mul, mul_assoc B]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, ← mass,
    show (∫ s in Ioi (0 : ℝ), s * rayWeight n s) = rawMoment n 1 by simp [rawMoment]]
  rw [moment]
  field_simp [(mass_pos hnNat).ne']

/-- The tail comparison before bounding the normalizing ratio and the first
moment at the tilted size. This applies to any nonnegative affine envelope. -/
theorem affine_tail_le {n N : ℕ} {r A B : ℝ} (hN : (3 / 2 : ℝ) < (N : ℝ)) (hNn : N ≤ n)
    (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ s in Ioi r, (A + B * s) * rayWeight n s) / mass n ≤
      mass N / mass n * (A + B * moment N 1) * ((1 + r)⁻¹) ^ (n - N) := by
  have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hn : 0 < n := by exact_mod_cast hnR
  let Q : ℝ := ((1 + r)⁻¹) ^ (n - N)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hi := affine_moment hN A B
  have sub : Ioi r ⊆ Ioi 0 := Ioi_subset_Ioi hr
  have hf : IntegrableOn (fun s => (A + B * s) * rayWeight n s) (Ioi r) :=
    (affine_moment (by linarith : (3 / 2 : ℝ) < (n : ℝ)) A B).1.mono_set sub
  have hg : IntegrableOn (fun s => Q * ((A + B * s) * rayWeight N s)) (Ioi r) :=
    (hi.1.mono_set sub).const_mul Q
  have hcomparison := setIntegral_mono_on hf hg measurableSet_Ioi (fun s hs => by
    have hs' : r < s := hs
    have hs0 : 0 ≤ s := hr.trans hs'.le
    have hsum : 0 < 1 + s := by positivity
    have hbase : (1 + s)⁻¹ ≤ (1 + r)⁻¹ :=
      (inv_le_inv₀ hsum (by positivity)).mpr (by linarith)
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + s)⁻¹) hbase (n - N)
    rw [rayWeight_shift hNn s, ← mul_assoc]
    rw [mul_comm Q]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity)
      (rayWeight_nonneg N hs0)))
  have hfull : (∫ s in Ioi r, (A + B * s) * rayWeight N s) ≤
      ∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight N s := by
    apply setIntegral_mono_set hi.1 _ sub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := (mem_Ioi.mp hs).le
    exact mul_nonneg (by positivity) (rayWeight_nonneg N hs0)
  rw [integral_const_mul] at hcomparison
  calc
    _ ≤ Q * (∫ s in Ioi r, (A + B * s) * rayWeight N s) / mass n :=
      div_le_div_of_nonneg_right hcomparison (mass_pos hn).le
    _ ≤ Q * (∫ s in Ioi (0 : ℝ), (A + B * s) * rayWeight N s) / mass n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfull hQ) (mass_pos hn).le
    _ = _ := by rw [hi.2]; dsimp [Q]; ring

/-- The normalized integral of the common affine tail envelope in (6) and (11). -/
theorem ray_tail_le {n : ℕ} (hn : 150 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in Ioi r, ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) * rayWeight n s) /
      mass n ≤ 60 * (n : ℝ) * ((1 + r)⁻¹) ^ CutBounds.cutExponent n := by
  let N := (n + 3) / 4
  have hNn : N ≤ n := by dsimp [N]; omega
  have hN : 2 ≤ N := by dsimp [N]; omega
  have h4N : n ≤ 4 * N := by dsimp [N]; omega
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h4N' : (n : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast h4N
  have hn' : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNr : 0 < (N : ℝ) := by linarith
  have hfirst : (3 / 2 : ℝ) < (N : ℝ) := by linarith
  let A : ℝ := 2 * (n : ℝ) + 1
  let B : ℝ := A * (n : ℝ) / 8
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM₁ : 0 ≤ moment N 1 := by
    rw [moment_one hfirst]
    exact div_nonneg (by norm_num) (by linarith)
  have hratio : mass N / mass n ≤ 16 := by
    have hdiv : (n : ℝ) / (N : ℝ) ≤ 4 := (div_le_iff₀ hNr).2 h4N'
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) / (N : ℝ)) hdiv 2
    norm_num at hpow
    exact (mass_ratio_le (by omega) hNn).trans hpow
  have hmoment : (n : ℝ) / 8 * moment N 1 ≤ 4 / 5 := by
    rw [moment_one hfirst, ← mul_div_assoc]
    exact (div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ) - 3 / 2)).2 (by linarith)
  have hlin s : (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8) = A + B * s := by
    dsimp [A, B]
    ring
  simp_rw [hlin]
  have hcoeff : A + B * moment N 1 ≤ A * (1 + 4 / 5) := by
    calc
      _ = A * (1 + (n : ℝ) / 8 * moment N 1) := by dsimp [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hA
  have hprod : (mass N / mass n) * (A + B * moment N 1) ≤ 60 * (n : ℝ) := by
    calc
      _ ≤ 16 * (A + B * moment N 1) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ 16 * (A * (1 + 4 / 5)) := mul_le_mul_of_nonneg_left hcoeff (by norm_num)
      _ ≤ _ := by dsimp [A]; linarith
  exact (affine_tail_le hfirst hNn hr hA hB).trans
    (mul_le_mul_of_nonneg_right hprod (by positivity))

/-- The integral tail after displacement one eighth is less than `1/50`. -/
theorem near_tail_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    (∫ s in Ioi (1 / 8 : ℝ), ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) *
      rayWeight n s) / mass n < 1 / 50 := by
  apply (ray_tail_le hn (show (0 : ℝ) ≤ 1 / 8 by norm_num)).trans_lt
  rw [show (1 + 1 / 8 : ℝ)⁻¹ = 8 / 9 by norm_num]
  simpa [CutBounds.tailScore] using CutBounds.near_tail_bound n hn

/-- The integral tail after displacement one sixth is less than `1/(20n)`. -/
theorem covariance_tail_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    (∫ s in Ioi (1 / 6 : ℝ), ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) *
      rayWeight n s) / mass n < 1 / (20 * (n : ℝ)) := by
  apply (ray_tail_le hn (show (0 : ℝ) ≤ 1 / 6 by norm_num)).trans_lt
  rw [show (1 + 1 / 6 : ℝ)⁻¹ = 6 / 7 by norm_num, ← div_div]
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ))).2
  convert CutBounds.covariance_tail_bound n hn using 1
  unfold CutBounds.tailScore
  ring

/-- The local quadratic envelope from (5), integrated against the actual
radial density up to displacement one eighth. -/
theorem near_local_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    IntegrableOn (fun s : ℝ =>
      ((2 * (n : ℝ) / 5 + 9) * s + (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * rayWeight n s)
      (Ioc 0 (1 / 8)) ∧
    (∫ s in Ioc (0 : ℝ) (1 / 8),
      ((2 * (n : ℝ) / 5 + 9) * s + (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * rayWeight n s) /
        mass n < 71 / 100 := by
  have hnN : 0 < n := by omega
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (((1 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  have h₂ : (((2 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  let A : ℝ := 2 * n / 5 + 9
  let B : ℝ := 2 * n / 5 + 4 / 5
  let F (s : ℝ) := A * (s ^ (1 : ℕ) * rayWeight n s) + B * (s ^ (2 : ℕ) * rayWeight n s)
  have hA := (integrableOn_moment h₁).const_mul A
  have hB := (integrableOn_moment h₂).const_mul B
  have hF : IntegrableOn F (Ioi 0) := hA.add hB
  have hle : (∫ s in Ioc (0 : ℝ) (1 / 8), F s) ≤ ∫ s in Ioi (0 : ℝ), F s := by
    apply setIntegral_mono_set hF _ Ioc_subset_Ioi_self.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 ≤ s := (mem_Ioi.mp hs).le
    have hweight := rayWeight_nonneg n hs'
    dsimp [F, A, B]
    positivity
  have hpoint s : (A * s + B * s ^ 2) * rayWeight n s = F s := by
    simp only [F, pow_one]
    ring
  refine ⟨(hF.mono_set Ioc_subset_Ioi_self).congr_fun
    (fun s _ => (hpoint s).symm) measurableSet_Ioc, ?_⟩
  change (∫ s in Ioc (0 : ℝ) (1 / 8), (A * s + B * s ^ 2) * rayWeight n s) /
    mass n < _
  simp_rw [hpoint]
  apply (div_le_div_of_nonneg_right hle (mass_pos hnN).le).trans_lt
  dsimp only [F]
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, ← rawMoment, ← rawMoment,
    add_div, mul_div_assoc, mul_div_assoc, ← moment, ← moment,
    moment_one (by linarith), moment_two (by linarith)]
  exact CutBounds.near_moment_bound hnR

end CatalanStrictPeaks.BetaMoments
