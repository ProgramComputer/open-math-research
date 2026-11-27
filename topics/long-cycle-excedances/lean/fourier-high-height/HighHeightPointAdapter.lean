import HighHeightNumerator

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

theorem localLogRatio_eq_quotient {s : ℝ} {z : ℂ} (hz : ‖z‖ < s) :
    localLogRatio s z =
      Complex.log ((1+Complex.exp (z-(s:ℂ)))/(1+Complex.exp (-(s:ℂ)))) := by
  let a := 1+Complex.exp (z-(s:ℂ))
  let b := 1+exp (-s)
  have hb : 0 < b := by dsimp [b]; positivity
  have he : (b:ℂ) = 1+Complex.exp (-(s:ℂ)) := by simp [b]
  have hE : ‖Complex.exp (z-(s:ℂ))‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith only [(Complex.re_le_norm z).trans_lt hz]
  have ha : a ≠ 0 := by
    intro h
    have H : Complex.exp (z-(s:ℂ)) = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [a,add_comm] using h
    rw [H, norm_neg, norm_one] at hE
    exact (lt_irrefl 1) hE
  change Complex.log a - Complex.log (1+Complex.exp (-(s:ℂ))) =
    Complex.log (a/(1+Complex.exp (-(s:ℂ))))
  rw [←he, div_eq_mul_inv, ←Complex.ofReal_inv, Complex.log_mul_ofReal _ (inv_pos.mpr hb) _ ha,
    Real.log_inv, Complex.ofReal_neg, Complex.ofReal_log hb.le]
  ring

theorem high_height_numerator_at_points (k : ℕ) (hk : 100 ≤ k)
    (s : ℝ) (hs : 0 < s) (hhigh : 16*(k:ℝ) < s^2)
    (g : ℕ → ℂ)
    (hG : ∀ i ∈ range (k-1),
      HasSum (fun a : ℕ => ((-exp (-s):ℝ):ℂ)^(a+1)*((a+1:ℕ):ℂ)^i)
        (-(g (i+1))*((i+1).factorial:ℂ)))
    (w : ℂ) :
    let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖w₁‖
    r ≤ ‖w‖ → ‖w‖ ≤ (1+1/(k:ℝ))*r →
    let w' := (((1-1/(k:ℝ))*r/‖w‖ : ℝ):ℂ)*w
    let w₁' := ((1-1/(k:ℝ):ℝ):ℂ)*w₁
    ‖numeratorLog k g w-localLogRatio s w'‖ +
      ‖numeratorLog k g w₁-localLogRatio s w₁'‖ < 25 := by
  let w₁ : ℂ := (s:ℂ)+(π:ℂ)*Complex.I
  let r := ‖w₁‖
  let R := ‖w‖
  change r ≤ R → R ≤ (1+1/(k:ℝ))*r → _
  intro hrR hR
  have hsq : r^2 = s^2+π^2 := by
    dsimp [r,w₁]
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  have hr : 0 ≤ r := norm_nonneg _
  have hr0 : 0 < r := by nlinarith [sq_nonneg π]
  have hR0 : 0 < R := hr0.trans_le hrR
  have hrc : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hRc : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR0.ne'
  let u := w/(R:ℂ)
  let v := w₁/(r:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0,R,hR0.ne']
  have hv : ‖v‖=1 := by simp [v,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,r,hr0.ne']
  have h1 : (R:ℂ)*u=w := by dsimp [u]; field_simp
  have h2 : (r:ℂ)*v=w₁ := by dsimp [v]; field_simp
  let t := (1-1/(k:ℝ))*r
  have h3 : (t:ℂ)*u=((t/R:ℝ):ℂ)*w := by
    dsimp [u]
    rw [Complex.ofReal_div]
    ring
  have h4 : (t:ℂ)*v=((1-1/(k:ℝ):ℝ):ℂ)*w₁ := by
    dsimp [v,t]
    rw [Complex.ofReal_mul]
    generalize hcoef : (1-1/(k:ℝ))=c
    field_simp [hrc]
    ring
  have H := high_height_numerator_contraction k hk s r R hs hr hhigh hsq hrR hR g hG hu hv
  change ‖numeratorLog k g ((R:ℂ)*u)-localLogRatio s ((t:ℂ)*u)‖ +
    ‖numeratorLog k g ((r:ℂ)*v)-localLogRatio s ((t:ℂ)*v)‖ < 25 at H
  simpa only [h1,h2,h3,h4] using H

#print axioms localLogRatio_eq_quotient
#print axioms high_height_numerator_at_points
end OpenMathResearch.LongCycleExcedances
