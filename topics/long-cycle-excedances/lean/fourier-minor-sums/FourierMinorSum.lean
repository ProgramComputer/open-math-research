import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- A circle at most twice the squared principal radius encloses no poles of
modulus at least three times that radius. At height zero these are precisely
all the nonprincipal odd poles. -/
theorem empty_minor_window {r R : ℝ} (hr : 0 < r)
    (hcap : R^2 ≤ r^2*2) (s : Finset ℕ) (w : ℕ → ℂ)
    (hl : ∀ i, 3*r ≤ ‖w i‖) (he : ∀ i ∈ s, ‖w i‖ ≤ R) : s = ∅ := by
  ext i
  constructor
  · intro hi
    exfalso
    have h := (hl i).trans (he i hi)
    nlinarith [sq_pos_of_pos hr, mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ R+3*r by linarith)]
  · simp

/-- An extra radial factor is present in the normalized coefficient residue.
The contrast multiplies that same residue by the pole ratio minus the
cosine. These bounds control both actual complex sums before pairing. -/
theorem normalized_minor_residue_sums {n : ℕ} {r S : ℝ} (hr : 0 ≤ r)
    (hS : 0 ≤ S) (C : ℂ) (w N : ℕ → ℂ) (principal : ℂ) (s : Finset ℕ)
    (hnear : ∀ i ∈ s, r ≤ ‖w i‖) (hpos : ∀ i ∈ s, 0 < ‖w i‖)
    (hcontrast : ∀ i ∈ s, ‖(r:ℂ)/w i-C‖ ≤ (2*(i+1:ℕ)+1:ℝ)*S) :
    let f (i : ℕ) := (r/‖w i‖)^n*‖N i/principal‖
    let u (i : ℕ) := (N i/(‖principal‖:ℂ))*((r:ℂ)/w i)^(n+1)
    (∑ i ∈ s, f i) ≤ 1/12 → (∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) ≤ 1/4 →
    ‖∑ i ∈ s, u i‖ ≤ 1/12 ∧ ‖∑ i ∈ s, ((r:ℂ)/w i-C)*u i‖ ≤ S/4 := by
  intro f u ho ha
  have hterm (i : ℕ) (hi : i ∈ s) : ‖u i‖ ≤ f i := by
    have hz : 0 ≤ r/‖w i‖ := div_nonneg hr (norm_nonneg _)
    have hz' : r/‖w i‖ ≤ 1 := (div_le_one (hpos i hi)).mpr (hnear i hi)
    have hpow := mul_le_of_le_one_right (pow_nonneg hz n) hz'
    dsimp only [u,f]
    rw [norm_mul,norm_pow,norm_div,norm_div,norm_div,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg (norm_nonneg _),pow_succ]
    calc
      _ ≤ (‖N i‖/‖principal‖)*(r/‖w i‖)^n := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := mul_comm _ _
  constructor
  · exact (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ho)
  · calc
      _ ≤ ∑ i ∈ s, ‖((r:ℂ)/w i-C)*u i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, S*((2*(i+1:ℕ)+1:ℝ)*f i) := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul]
        calc
          _ ≤ ((2*(i+1:ℕ)+1:ℝ)*S)*f i := mul_le_mul (hcontrast i hi) (hterm i hi) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ = S*(∑ i ∈ s, (2*(i+1:ℕ)+1:ℝ)*f i) := (mul_sum ..).symm
      _ ≤ S/4 := by linarith only [mul_le_mul_of_nonneg_left ha hS]

/-- Add the boundary error to the real part of the paired residues. The two
errors use the same principal phase and the same normalization. -/
theorem paired_fourier_error_margin {S old next C b d : ℝ} {u v v' : ℂ}
    (ho : old=u.re+v.re+b)
    (ha : next-C*old=S*u.im+v'.re+d)
    (hminor : ‖v‖ ≤ 1/12) (hminor' : ‖v'‖ ≤ S/4)
    (hb : |b| < 1/25) (hd : |d| < S/25) :
    |old-u.re| < 37/300 ∧ |next-C*old-S*u.im| < (29/100)*S := by
  have h₀ := abs_add_le v.re b
  have h₁ := abs_add_le v'.re d
  have e₀ : old-u.re=v.re+b := by linarith only [ho]
  have e₁ : next-C*old-S*u.im=v'.re+d := by linarith only [ha]
  rw [e₀,e₁]
  constructor
  · linarith only [h₀, (Complex.abs_re_le_norm v).trans hminor, hb]
  · linarith only [h₁, (Complex.abs_re_le_norm v').trans hminor', hd]

/-- At an old zero the principal sine has magnitude greater than 99/100,
and the next row has its sign. -/
theorem paired_fourier_sign_at_zero {S next : ℝ} {u : ℂ} (hS : 0 < S)
    (hunit : ‖u‖=1) (hold : |u.re| < 37/300)
    (hnext : |next-S*u.im| < (29/100)*S) :
    99/100 < |u.im| ∧ 0 < next*u.im := by
  have hc : u.re^2+u.im^2=1 := by
    have h := Complex.sq_norm u
    rw [hunit,one_pow,Complex.normSq_apply] at h
    nlinarith only [h]
  have hre := (sq_lt_sq₀ (abs_nonneg u.re) (by norm_num)).mpr hold
  rw [sq_abs] at hre
  have hi : 99/100 < |u.im| := by
    by_contra! hh
    have hh' := (sq_le_sq₀ (abs_nonneg u.im) (by norm_num)).mpr hh
    rw [sq_abs] at hh'
    nlinarith only [hc,hre,hh']
  refine ⟨hi,?_⟩
  obtain ⟨hl,hu⟩ := abs_lt.mp hnext
  rcases le_or_gt 0 u.im with hp | hn
  · rw [abs_of_nonneg hp] at hi
    apply mul_pos _ (by linarith only [hi])
    nlinarith only [hl, mul_lt_mul_of_pos_left hi hS,hS]
  · rw [abs_of_neg hn] at hi
    apply mul_pos_of_neg_of_neg _ hn
    nlinarith only [hu, mul_lt_mul_of_pos_left hi hS,hS]

#print axioms paired_fourier_error_margin
#print axioms paired_fourier_sign_at_zero
#print axioms empty_minor_window
#print axioms normalized_minor_residue_sums
end OpenMathResearch.LongCycleExcedances
