import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real

/-- A gap in the exponential's argument gives a denominator bound at every
height. Principal logarithm supplies a preimage closest enough for the estimate. -/
theorem exponential_period_gap (v : ℂ) {δ : ℝ} (hd : 0 ≤ δ)
    (hgap : ∀ l : ℤ, δ ≤ ‖v-(l:ℂ)*(2*π*I)‖) :
    δ/(1+δ) ≤ ‖1-Complex.exp v‖ := by
  let e := Complex.exp v-1
  have hn : ‖1-Complex.exp v‖ = ‖e‖ := norm_sub_rev _ _
  rw [hn]
  have hp : 0 < 1+δ := by linarith
  by_cases h : ‖e‖ < 1
  · have hd' : δ ≤ ‖Complex.log (Complex.exp v)‖ := by
      obtain ⟨l,hl⟩ := Complex.exp_eq_exp_iff_exists_int.mp (Complex.exp_log (Complex.exp_ne_zero v)).symm
      have he : v-(l:ℂ)*(2*π*I) = Complex.log (Complex.exp v) := by linear_combination hl
      simpa only [he] using hgap l
    have hlog := Complex.norm_log_sub_logTaylor_le 0 h
    have h1 : (1:ℂ)+e = Complex.exp v := by dsimp only [e]; ring
    have hbound : ‖Complex.log (Complex.exp v)‖ ≤ ‖e‖/(1-‖e‖) := by
      simpa [Complex.logTaylor,h1,div_eq_mul_inv] using hlog
    have hpos : 0 < 1-‖e‖ := sub_pos.mpr h
    have ha := (le_div_iff₀ hpos).mp (hd'.trans hbound)
    exact (div_le_iff₀ hp).mpr (by linarith)
  · exact ((div_le_one hp).mpr (by linarith)).trans (le_of_not_gt h)

/-- The positive logistic denominator is bounded in terms of the distance
to every member of its actual signed odd pole lattice. -/
theorem odd_logistic_denominator_gap (v : ℂ) {δ : ℝ} (hd : 0 ≤ δ)
    (hgap : ∀ l : ℤ, δ ≤ ‖v-(2*(l:ℂ)+1)*π*I‖) :
    δ/(1+δ) ≤ ‖1+Complex.exp v‖ := by
  have h := exponential_period_gap (v+(π:ℂ)*I) hd (fun l => by
    have he : v+(π:ℂ)*I-(l:ℂ)*(2*π*I) = v-(2*((l-1:ℤ):ℂ)+1)*π*I := by push_cast; ring
    rw [he]
    exact hgap (l-1))
  simpa [Complex.exp_add,Complex.exp_pi_mul_I] using h

private theorem exp_left_contraction {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp z-Complex.exp w‖ ≤ ‖z-w‖ := by
  have he := (convex_halfSpace_re_le (r:=0)).norm_image_sub_le_of_norm_deriv_le
    (f:=Complex.exp) (C:=1) (fun x _ => (Complex.hasDerivAt_exp x).differentiableAt)
    (fun x hx => by rw [(Complex.hasDerivAt_exp x).deriv,Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hx)
    hw hz
  simpa using he

private theorem ratio_from_difference (N D : ℂ) {γ Δ : ℝ} (hg : 0 < γ)
    (hd : γ ≤ ‖D‖) (hΔ : ‖N-D‖ ≤ Δ) : ‖N‖/‖D‖ ≤ 1+Δ/γ := by
  have hn : 0 < ‖D‖ := hg.trans_le hd
  have he : ‖N‖ ≤ ‖D‖+Δ := by
    have := norm_sub_norm_le N D
    linarith
  calc
    _ ≤ (‖D‖+Δ)/‖D‖ := div_le_div_of_nonneg_right he hn.le
    _ = 1+Δ/‖D‖ := by rw [add_div,div_self hn.ne']
    _ ≤ _ := add_le_add_left (div_le_div_of_nonneg_left ((norm_nonneg _).trans hΔ) hg hd) _

/-- When the real parts contract towards the pole line as on the comparison
radii, the ratio of denominators has a global bound with loss (1+δ)/δ. -/
theorem odd_logistic_contraction (v b : ℂ) {δ : ℝ} (hd : 0 < δ)
    (hgap : ∀ l : ℤ, δ ≤ ‖v-(2*(l:ℂ)+1)*π*I‖)
    (hdir : b.re ≤ v.re ∨ (b.re ≤ 0 ∧ v.re ≤ 0)) :
    ‖1+Complex.exp b‖ / ‖1+Complex.exp v‖ ≤ 1+‖b-v‖/(δ/(1+δ)) := by
  have hg : 0 < δ/(1+δ) := by positivity
  rcases hdir with h | ⟨hb,hv⟩
  · have hn := odd_logistic_denominator_gap (-v) hd.le (fun l => by
      have e : -v-(2*(l:ℂ)+1)*π*I = -(v-(2*((-l-1:ℤ):ℂ)+1)*π*I) := by push_cast; ring
      rw [e,norm_neg]
      exact hgap (-l-1))
    have hc := exp_left_contraction (z:=b-v) (w:=0) (by simpa using sub_nonpos.mpr h) (by simp)
    have he := ratio_from_difference (Complex.exp (-v)+Complex.exp (b-v))
      (Complex.exp (-v)+1) hg (by simpa only [add_comm] using hn)
      (Δ:=‖b-v‖) (by simpa using hc)
    have hm (z : ℂ) : (1+Complex.exp z)*Complex.exp (-v) =
        Complex.exp (-v)+Complex.exp (z-v) := by
      rw [add_mul,one_mul,←Complex.exp_add,sub_eq_add_neg]
    have hs : (1+Complex.exp v)*Complex.exp (-v) = Complex.exp (-v)+1 := by
      rw [hm,sub_self,Complex.exp_zero]
    rw [←hm b,←hs,norm_mul,norm_mul,mul_div_mul_right _ _ (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))] at he
    exact he
  · apply ratio_from_difference _ _ hg (odd_logistic_denominator_gap v hd.le hgap)
    simpa using exp_left_contraction hb hv

/-- Contracting a point toward the origin gives the quotient needed on
the two comparison radii. The gap is the ordinary distance to each pole. -/
theorem original_contracted_circle_ratio {s α δ : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ α)
    (hα : α ≤ 1) (hd : 0 < δ) (w : ℂ)
    (hgap : ∀ l : ℤ, δ ≤ ‖w-((s:ℂ)+(2*(l:ℂ)+1)*π*I)‖) :
    ‖1+Complex.exp ((α:ℂ)*w-s)‖ / ‖1+Complex.exp (w-s)‖ ≤
      1 + ‖(α:ℂ)*w-w‖*(1+δ)/δ := by
  have hg (l : ℤ) : δ ≤ ‖w-s-(2*(l:ℂ)+1)*π*I‖ := by
    rw [sub_sub]
    exact hgap l
  have he := odd_logistic_contraction (w-s) ((α:ℂ)*w-s) hd hg (by
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero]
    by_cases hw : 0 ≤ w.re
    · exact Or.inl (by nlinarith [mul_le_mul_of_nonneg_right hα hw])
    · exact Or.inr ⟨by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hw)],
        by linarith⟩)
  rw [sub_sub_sub_cancel_right] at he
  simpa only [div_div_eq_mul_div] using he

#print axioms original_contracted_circle_ratio
#print axioms odd_logistic_contraction
#print axioms exponential_period_gap
#print axioms odd_logistic_denominator_gap
end OpenMathResearch.LongCycleExcedances
