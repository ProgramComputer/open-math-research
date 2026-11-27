import PoleModeIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Set

private theorem vertical_norm_sq (x v : ℝ) : ‖verticalArgument x v‖^2 = x^2+v^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [verticalArgument,Complex.add_re,Complex.add_im,Complex.mul_I_im,Complex.mul_I_re]
  ring

theorem segment_in_radius {x l u R : ℝ} (hl : ‖verticalArgument x l‖ ≤ R)
    (hu : ‖verticalArgument x u‖ ≤ R) (v : ℝ) (hv : v ∈ Icc l u) :
    ‖verticalArgument x v‖ ≤ R := by
  apply le_of_sq_le_sq _ ((norm_nonneg _).trans hl)
  rw [vertical_norm_sq]
  by_cases hp : 0 ≤ v
  · have h := pow_le_pow_left₀ (norm_nonneg _) hu 2
    rw [vertical_norm_sq] at h
    linarith only [pow_le_pow_left₀ hp hv.2 2,h]
  · have h := pow_le_pow_left₀ (norm_nonneg _) hl 2
    rw [vertical_norm_sq] at h
    have h' := pow_le_pow_left₀ (neg_nonneg.mpr (lt_of_not_ge hp).le) (neg_le_neg hv.1) 2
    nlinarith only [h,h']

theorem coherent_log_chord_bound {k : ℕ} (hk : 7 ≤ k) {x r l u : ℝ} (hx : 10*√(k:ℝ) ≤ x)
    (hr : 0 ≤ r) (hrsq : r^2=x^2+π^2) (hlu : l < u)
    (hl : ‖verticalArgument x l‖ ≤ r*(1+1/(50*(k:ℝ))))
    (hu : ‖verticalArgument x u‖ ≤ r*(1+1/(50*(k:ℝ))))
    (t : ℂ) (el : Complex.exp (-verticalArgument x l)=t) (eu : Complex.exp (-verticalArgument x u)=t)
    (g : ℕ → ℂ) (coeff : ∀ j ∈ Finset.range (k-1),
      HasSum (fun i : ℕ => t^(i+1)*((i+1:ℕ):ℂ)^j) (-g (j+1)*((j+1).factorial:ℂ))) :
    π*‖logPolyAt (k-1) g (verticalArgument x u)-logPolyAt (k-1) g (verticalArgument x l)‖ <
      (12/25)*(u-l) := by
  rw [log_difference_from_modes (k-1) g x l u t eu el coeff,norm_neg]
  exact (coherent_vertical_transport hk hx hr hrsq hlu (segment_in_radius hl hu)).2

theorem conjugate_logPolyAt (m : ℕ) (g : ℕ → ℝ) (z : ℂ) :
    logPolyAt m (fun d => (g d:ℂ)) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (logPolyAt m (fun d => (g d:ℂ)) z) := by
  simp [logPolyAt,map_sum,map_mul,map_pow,Complex.conj_ofReal]

#print axioms coherent_log_chord_bound
#print axioms conjugate_logPolyAt
end OpenMathResearch.LongCycleExcedances
