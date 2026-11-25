import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Angular bounds used to locate the principal poles of the ordered
partition row generating function at each fixed threshold at least four. -/

namespace OrderedGlobalAngular

open Real Set
open scoped BigOperators

private theorem sine_chord {x t : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ π)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : t*sin x ≤ sin (t*x) := by
  rcases hx₀.eq_or_lt with rfl | hx
  · simp
  rcases ht₀.eq_or_lt with rfl | ht
  · simp
  rcases ht₁.eq_or_lt with rfl | ht'
  · simp
  let y := t*x
  have hy : 0 < y := mul_pos ht hx
  have hyx : y < x := by
    dsimp [y]
    simpa only [one_mul] using mul_lt_mul_of_pos_right ht' hx
  obtain ⟨u, hu, hdu⟩ := exists_hasDerivAt_eq_slope sin cos hy
    continuous_sin.continuousOn (fun z _ => hasDerivAt_sin z)
  obtain ⟨v, hv, hdv⟩ := exists_hasDerivAt_eq_slope sin cos hyx
    continuous_sin.continuousOn (fun z _ => hasDerivAt_sin z)
  simp only [sin_zero, sub_zero] at hdu
  have hcos := cos_le_cos_of_nonneg_of_le_pi hu.1.le (hv.2.le.trans hxπ)
    (hu.2.trans hv.1).le
  rw [hdu, hdv] at hcos
  have hs := (div_le_div_iff₀ (sub_pos.mpr hyx) hy).mp hcos
  have hs' : y*sin x ≤ x*sin y := by nlinarith only [hs]
  apply (mul_le_mul_right hx).mp
  dsimp [y] at hs' ⊢
  nlinarith only [hs']

private noncomputable def weight (j k : ℕ) : ℝ :=
  (1 - (k : ℝ)/(j : ℝ)) / (k.factorial : ℝ)

theorem sector_weight_lower_bound {j : ℕ} (hj : 4 ≤ j) :
    25/24 ≤ ∑ k ∈ Finset.Icc 1 (j-1), weight j k := by
  have hsubset : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 (j-1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl | rfl := hk <;> exact Finset.mem_Icc.mpr (by omega)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset (f := weight j) (by
    intro k hk _
    have hk' : (k : ℝ) ≤ j := by
      exact_mod_cast (show k ≤ j by have := (Finset.mem_Icc.mp hk).2; omega)
    have hj₀ : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    exact div_nonneg (sub_nonneg.mpr ((div_le_iff₀ hj₀).2 (by simpa using hk')))
      (Nat.cast_nonneg _))
  have hjR : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : 0 < (j : ℝ) := by linarith
  have hd : (1 : ℝ) / j ≤ 1/4 := by
    apply (div_le_iff₀ hj₀).2
    linarith only [hjR]
  have hexact : ∑ k ∈ ({1, 2, 3} : Finset ℕ), weight j k =
      5/3 - (5/2)*(1/(j : ℝ)) := by
    norm_num [weight, Nat.factorial]; ring
  apply le_trans _ hsum
  rw [hexact]
  linarith only [hd]

/-- The scalar imaginary part of the rotated numerator is strictly signed
on the unit-radius boundary of the principal sector. -/
theorem sector_boundary_sines {j : ℕ} (hj : 4 ≤ j) {theta : ℝ}
    (hpos : 0 < theta) (hangle : (j : ℝ)*theta < π) :
    sin ((j : ℝ)*theta) <
      ∑ k ∈ Finset.Icc 1 (j-1), sin (((j : ℝ)-(k : ℝ))*theta) / (k.factorial : ℝ) := by
  have hj₀ : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hs : 0 < sin ((j : ℝ)*theta) :=
    sin_pos_of_pos_of_lt_pi (mul_pos hj₀ hpos) hangle
  calc
    _ < (25/24) * sin ((j : ℝ)*theta) := by nlinarith only [hs]
    _ ≤ (∑ k ∈ Finset.Icc 1 (j-1), weight j k) * sin ((j : ℝ)*theta) :=
      mul_le_mul_of_nonneg_right (sector_weight_lower_bound hj) hs.le
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : (k : ℝ) ≤ j := by
        exact_mod_cast (show k ≤ j by have := (Finset.mem_Icc.mp hk).2; omega)
      have h₀ : 0 ≤ 1-(k : ℝ)/(j : ℝ) :=
        sub_nonneg.mpr ((div_le_iff₀ hj₀).2 (by simpa using hk'))
      have h₁ : 1-(k : ℝ)/(j : ℝ) ≤ 1 := by
        linarith only [div_nonneg (Nat.cast_nonneg k) hj₀.le]
      have h := sine_chord (mul_nonneg hj₀.le hpos.le) hangle.le h₀ h₁
      have he : (1-(k : ℝ)/(j : ℝ))*((j : ℝ)*theta) =
          ((j : ℝ)-(k : ℝ))*theta := by
        field_simp [hj₀.ne']; ring
      rw [he] at h
      simpa only [weight, div_mul_eq_mul_div] using
        div_le_div_of_nonneg_right h (Nat.cast_nonneg k.factorial)

private noncomputable def turn (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ)*Complex.I)

/-- The complex rotated numerator has strictly negative imaginary part on the
unit-radius boundary of the principal sector. -/
theorem rotated_numerator_im_negative {j : ℕ} (hj : 4 ≤ j) {theta : ℝ}
    (hpos : 0 < theta) (hangle : (j : ℝ)*theta < π) :
    (((-1 : ℂ) +
      ∑ k ∈ Finset.Icc 1 (j-1), turn ((k : ℝ)*theta) / ((k.factorial : ℝ) : ℂ)) *
      turn (-(j : ℝ)*theta)).im < 0 := by
  have hterm (k : ℕ) :
      (turn ((k : ℝ)*theta) / ((k.factorial : ℝ) : ℂ) * turn (-(j : ℝ)*theta)).im =
        -sin (((j : ℝ)-(k : ℝ))*theta) / (k.factorial : ℝ) := by
    have hprod : turn ((k : ℝ)*theta) * turn (-(j : ℝ)*theta) =
        turn (-(((j : ℝ)-(k : ℝ))*theta)) := by
      unfold turn
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [div_mul_eq_mul_div, hprod, Complex.div_ofReal_im, turn, Complex.exp_ofReal_mul_I_im, sin_neg]
  have hconstant : ((-1 : ℂ)*turn (-(j : ℝ)*theta)).im = sin ((j : ℝ)*theta) := by
    rw [neg_mul, one_mul, Complex.neg_im, turn, Complex.exp_ofReal_mul_I_im, neg_mul, sin_neg, neg_neg]
  rw [add_mul, Finset.sum_mul, Complex.add_im, Complex.im_sum, hconstant]
  simp_rw [hterm, neg_div, Finset.sum_neg_distrib]
  linarith only [sector_boundary_sines hj hpos hangle]

/-- The negative imaginary part of a rotated value gives strict angular
order when both principal angles lie between zero and pi. -/
theorem angle_lt_of_sin_sub_neg {a t : ℝ}
    (ht₀ : 0 < t) (haπ : a < π) (him : sin (a-t) < 0) :
    a < t := by
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr h)
    (by linarith only [haπ, ht₀]))) him

theorem abs_sin_nat_multiple_le (k : ℕ) (theta : ℝ) :
    |sin ((k : ℝ)*theta)| ≤ (k : ℝ)*|sin theta| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc
      _ ≤ |sin ((k : ℝ)*theta)*cos theta| + |cos ((k : ℝ)*theta)*sin theta| :=
        abs_add_le _ _
      _ ≤ |sin ((k : ℝ)*theta)| + |sin theta| := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _))
      _ ≤ _ := by nlinarith only [ih]

private theorem sin_double_lower {theta : ℝ} (hpos : 0 < theta) (hangle : theta ≤ π/3) :
    sin theta ≤ sin (2*theta) := by
  have hcos := cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [pi_pos]) hangle
  rw [cos_pi_div_three] at hcos
  have hsin := sin_pos_of_pos_of_lt_pi hpos (by linarith [pi_pos] : theta < π)
  rw [sin_two_mul]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hcos) hsin.le]

/-- The first Fourier coefficients and the quadratic tail moment force the
strict derivative sign on the first third of a semicircle. -/
theorem first_sector_derivative_positive
    (tail : Finset ℕ) (c : ℕ → ℝ) {r theta : ℝ}
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hpos : 0 < theta) (hangle : theta ≤ π/3)
    (hc₁ : (35/100)*r ≤ c 1) (hc₂ : (30/100)*r^2 ≤ c 2) (hc₃ : 0 ≤ c 3)
    (hcn : ∀ k ∈ tail, 0 ≤ c k)
    (hmoment : ∑ k ∈ tail, (k : ℝ)^2*c k ≤ (94/100)*r^4) :
    0 < c 1*sin theta + 2*c 2*sin (2*theta) + 3*c 3*sin (3*theta) +
      ∑ k ∈ tail, (k : ℝ)*c k * sin ((k : ℝ)*theta) := by
  have hsin := sin_pos_of_pos_of_lt_pi hpos (by linarith [pi_pos] : theta < π)
  have hsin3 : 0 ≤ sin (3*theta) :=
    sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith only [hangle])
  have htail : -(∑ k ∈ tail, (k : ℝ)^2*c k)*sin theta ≤
      ∑ k ∈ tail, (k : ℝ)*c k*sin ((k : ℝ)*theta) := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hs := abs_sin_nat_multiple_le k theta
    rw [abs_of_nonneg hsin.le] at hs
    have hlow : -(k : ℝ)*sin theta ≤ sin ((k : ℝ)*theta) := by
      simpa only [neg_mul] using (abs_le.mp hs).1
    have hmul := mul_le_mul_of_nonneg_left hlow
      (mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k : ℝ)) (hcn k hk))
    nlinarith only [hmul]
  have h₁ := mul_le_mul_of_nonneg_right hc₁ hsin.le
  have h₂ := mul_le_mul_of_nonneg_right hc₂ hsin.le
  have h₂pos : 0 ≤ c 2 := (mul_nonneg (by norm_num) (sq_nonneg r)).trans hc₂
  have h₂sin := mul_le_mul_of_nonneg_left (sin_double_lower hpos hangle)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₂pos)
  have h₃ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hc₃) hsin3
  have hM := mul_le_mul_of_nonneg_right hmoment hsin.le
  have hR1 : r^4 ≤ r := by
    simpa only [pow_one] using pow_le_pow_of_le_one hr₀.le hr₁
      (show 1 ≤ 4 by norm_num)
  have hR2 : r^4 ≤ r^2 := pow_le_pow_of_le_one hr₀.le hr₁ (show 2 ≤ 4 by norm_num)
  have hR1s := mul_le_mul_of_nonneg_right hR1 hsin.le
  have hR2s := mul_le_mul_of_nonneg_right hR2 hsin.le
  have hp := mul_pos (pow_pos hr₀ 4) hsin
  nlinarith only [h₁, h₂, h₂sin, h₃, hM, htail, hR1s, hR2s, hp]

end OrderedGlobalAngular
