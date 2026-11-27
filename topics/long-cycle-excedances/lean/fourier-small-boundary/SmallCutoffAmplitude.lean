import SmallCutoffCircle
import FourierNormComparison

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory

open private annular_displacement from FourierSelectedAmplitude in
/-- Cauchy's supremum estimate only requires a polynomial loss on the circle
for finite cutoffs at large sizes. -/
theorem small_cutoff_amplitude {n k s R M : ℝ} (hn : 10000≤n) (hk : 8≤k) (hk' : k≤100)
    (hs : 0≤s) (G : ℂ → ℂ) (w : ℂ) (hw : ‖w‖=R) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let α := (1-1/k)*r/R
    1≤n*(π/r)^2 → r≤R → R≤(1+1/k)*r →
    (∀ l : ℤ, r/n≤‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I)‖) →
    ‖G w-diskLogisticLog s ((α:ℂ)*w)‖+‖G p-diskLogisticLog s (((1-1/k:ℝ):ℂ)*p)‖≤M →
    r*‖Complex.exp (G w)/(1+Complex.exp (w-s))‖/‖Complex.exp (G p)‖ ≤
      2*n^2*exp M := by
  intro p r α hm hrR hR hgap hG
  have hn0 : 0<n := by linarith
  have hk1 : 1<k := by linarith
  have hk0 : 0<k := by linarith
  have hr2 : r^2=s^2+π^2 := by
    dsimp [r,p]; rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hr : 0<r := by nlinarith [norm_nonneg p,sq_pos_of_pos pi_pos]
  have hd : 0<r/n := div_pos hr hn0
  have hrn : r≤n := by
    rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),one_mul] at hm
    have hπ : π^2 ≤ (4:ℝ)^2 := pow_le_pow_left₀ pi_pos.le (by linarith only [pi_lt_d4]) 2
    apply le_of_sq_le_sq _ hn0.le
    exact hm.trans ((mul_le_mul_of_nonneg_left hπ hn0.le).trans (by nlinarith only [mul_nonneg hn0.le (by linarith : 0≤n-16)]))
  have hd1 : r/n≤1 := (div_le_one hn0).mpr hrn
  let Δ := ‖(α:ℂ)*w-w‖
  have hΔ : Δ≤2*(r/k) := by
    have h := annular_displacement hr hk1 w (hw ▸ hrR) (hw ▸ hR)
    simpa only [hw] using h
  have hratio : 1+Δ*(1+r/n)/(r/n) ≤ n := by
    have h : Δ*(1+r/n) ≤ 4*(r/k) := by
      calc
        _ ≤ (2*(r/k))*2 := mul_le_mul hΔ (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    have hdv : Δ*(1+r/n)/(r/n) ≤ 4*(n/k) := (div_le_iff₀ hd).mpr
      (h.trans_eq (by field_simp <;> ring))
    have hv : n/k≤n/8 := div_le_div_of_nonneg_left hn0.le (by norm_num) hk
    linarith
  have H := annular_amplitude_from_contraction hs hk1 hd G w hgap (hw ▸ hrR)
    (by simpa only [hw] using hG)
  have hp := principal_point_denominator (s:=s) hk1.le
  have hq : 0<r/k/(1+r/k) := by positivity
  rw [hw] at H
  apply H.trans
  calc
    _ ≤ (r*exp M*n)/(r/k/(1+r/k)) := by
      apply div_le_div₀ (by positivity) _ hq hp
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = ((k+r)*n)*exp M := by field_simp <;> ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      nlinarith only [mul_le_mul_of_nonneg_right (show k+r≤2*n by linarith) hn0.le]

open private circleWave_norm from FourierNormComparison in
theorem normalized_coefficient_le_sup {f : ℝ → ℂ} {M : ℝ} (hf : ∀ x, ‖f x‖ ≤ M) (j : ℤ) :
    ‖normalizedFourierIntegral f j‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 2*π)
    (f := fun x => circleWave (-j) x*f x) (C := M) (fun x _ => by
      rw [norm_mul,circleWave_norm,one_mul]; exact hf x)
  rw [sub_zero,abs_of_pos two_pi_pos] at h
  unfold normalizedFourierIntegral
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pi_pos]
  norm_num
  exact (div_le_iff₀ two_pi_pos).mpr h

#print axioms small_cutoff_amplitude
#print axioms normalized_coefficient_le_sup
end OpenMathResearch.LongCycleExcedances
