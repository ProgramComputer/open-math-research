import FourierDiskLog
import FourierLogarithmicGap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Comparison at two angles from a single budget for the two logarithmic errors. -/
theorem disk_amplitude_comparison {s r M B : ℝ} (hs : 0 ≤ s) (hr2 : r^2=s^2+π^2)
    (G : ℂ → ℂ) (w p u v : ℂ) (hu : ‖u‖ < r) (hv : ‖v‖ < r)
    (herr : ‖G w - diskLogisticLog s u‖ + ‖G p - diskLogisticLog s v‖ ≤ M)
    (hw : 1+Complex.exp (w-s) ≠ 0)
    (hB : ‖1+Complex.exp (u-s)‖ / ‖1+Complex.exp (w-s)‖ ≤ B) :
    r * ‖Complex.exp (G w)/(1+Complex.exp (w-s))‖ / ‖Complex.exp (G p)‖ ≤
      r * Real.exp M * B / ‖1+Complex.exp (v-s)‖ := by
  let L := diskLogisticLog s
  have rr : 0 < r := (norm_nonneg _).trans_lt hv
  have he : ‖Complex.exp ((G w-L u)-(G p-L v))‖ ≤ Real.exp M := by
    rw [Complex.norm_exp,Real.exp_le_exp]
    apply le_trans _ herr
    exact (Complex.re_le_norm _).trans (norm_sub_le _ _)
  have hn (x : ℂ) (hx : ‖x‖ < r) := congrArg norm (diskLogisticLog_normalized hs hr2 hx)
  have heq : Complex.exp ((G w-L u)-(G p-L v)) =
      Complex.exp (G w)/Complex.exp (L u)/(Complex.exp (G p)/Complex.exp (L v)) := by
    simp only [Complex.exp_sub]
  have hc : 1+Complex.exp (-(s:ℂ)) ≠ 0 := by
    have hp : (0:ℝ) < 1+Real.exp (-s) := by positivity
    simpa using (Complex.ofReal_ne_zero.mpr hp.ne')
  have hp (x : ℂ) (hx : ‖x‖ < r) : 0 < ‖1+Complex.exp (x-s)‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hh := diskLogisticLog_normalized hs hr2 hx
    rw [h,zero_div] at hh
    exact Complex.exp_ne_zero _ hh
  have H : ‖Complex.exp (G w)/(1+Complex.exp (w-s))‖ / ‖Complex.exp (G p)‖ =
      ‖Complex.exp ((G w-L u)-(G p-L v))‖ *
        (‖1+Complex.exp (u-s)‖/‖1+Complex.exp (w-s)‖) / ‖1+Complex.exp (v-s)‖ := by
    rw [heq]
    simp only [norm_div,L,hn u hu,hn v hv,norm_div]
    have cancel (A C D E F J : ℝ) (hC : C ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0)
        (hF : F ≠ 0) (hJ : J ≠ 0) :
        A/J/C = (A/(D/E)/(C/(F/E)))*(D/J)/F := by field_simp; ring
    exact cancel _ _ _ _ _ _ (norm_ne_zero_iff.mpr (Complex.exp_ne_zero (G p)))
      (hp u hu).ne' (norm_ne_zero_iff.mpr hc) (hp v hv).ne' (norm_ne_zero_iff.mpr hw)
  calc
    _ = r*(‖Complex.exp ((G w-L u)-(G p-L v))‖ *
          (‖1+Complex.exp (u-s)‖/‖1+Complex.exp (w-s)‖)/‖1+Complex.exp (v-s)‖) := by
        rw [← H,mul_div_assoc]
    _ ≤ r*(Real.exp M * B / ‖1+Complex.exp (v-s)‖) := by
        apply mul_le_mul_of_nonneg_left _ rr.le
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul he hB (div_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos M).le
    _ = _ := by ring

/-- The annular bound at its original two points, with the principal denominator
and the loss from the same circle's pole separation explicit. -/
theorem annular_amplitude_from_contraction {s K δ M : ℝ} (hs : 0 ≤ s) (hk : 1 < K)
    (hd : 0 < δ) (G : ℂ → ℂ) (w : ℂ)
    (hgap : ∀ l : ℤ, δ ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*Complex.I)‖) :
    let p := (s:ℂ)+(π:ℂ)*Complex.I
    let r := ‖p‖
    let α := (1-1/K)*r/‖w‖
    r ≤ ‖w‖ →
    ‖G w - diskLogisticLog s ((α:ℂ)*w)‖ +
      ‖G p - diskLogisticLog s (((1-1/K:ℝ):ℂ)*p)‖ ≤ M →
    r * ‖Complex.exp (G w)/(1+Complex.exp (w-s))‖ / ‖Complex.exp (G p)‖ ≤
      r * Real.exp M * (1+‖(α:ℂ)*w-w‖*(1+δ)/δ) / ‖1-Complex.exp (-p/(K:ℂ))‖ := by
  intro p r α hw herr
  have hsq : r^2 = s^2+π^2 := by
    dsimp [r,p]; rw [Complex.sq_norm,Complex.normSq_apply]; simp; ring
  have hr : 0 < r := by nlinarith [norm_nonneg p,sq_pos_of_pos Real.pi_pos]
  have hK : 0 < K := by linarith
  have hfrac : 0 < 1/K := by positivity
  have hb : 0 ≤ 1-1/K := sub_nonneg.mpr ((div_le_one hK).mpr hk.le)
  have hR := hr.trans_le hw
  have hα : 0 ≤ α := div_nonneg (mul_nonneg hb hr.le) hR.le
  have hα1 : α ≤ 1 := (div_le_one hR).mpr (by nlinarith [mul_pos hfrac hr])
  have hnorm : (1-1/K)*r < r := by nlinarith [mul_pos hfrac hr]
  have hu : ‖(α:ℂ)*w‖ < r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα]
    simpa only [α, div_mul_cancel₀ _ hR.ne'] using hnorm
  have hv : ‖(((1-1/K:ℝ):ℂ)*p)‖ < r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
    exact hnorm
  have hγ := odd_logistic_denominator_gap (w-s) hd.le (fun l => by
    rw [sub_sub]; exact hgap l)
  have hn : 1+Complex.exp (w-s) ≠ 0 := norm_pos_iff.mp
    ((div_pos hd (by linarith)).trans_le hγ)
  have he : (((1-1/K:ℝ):ℂ)*p)-s = (π:ℂ)*Complex.I + (-p/(K:ℂ)) := by
    dsimp [p]; push_cast; ring
  have H := disk_amplitude_comparison hs hsq G w p _ _ hu hv herr hn
    (original_contracted_circle_ratio hs hα hα1 hd w hgap)
  have hD : 1+Complex.exp ((((1-1/K:ℝ):ℂ)*p)-s) = 1-Complex.exp (-p/(K:ℂ)) := by
    rw [he,Complex.exp_add,Complex.exp_pi_mul_I,neg_one_mul,sub_eq_add_neg]
  rw [hD] at H
  exact H

#print axioms annular_amplitude_from_contraction
#print axioms disk_amplitude_comparison
end OpenMathResearch.LongCycleExcedances
