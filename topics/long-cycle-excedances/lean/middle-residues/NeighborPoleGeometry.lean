import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Removing the principal real direction from a neighboring residue
introduces at most the odd-pole weight times the principal sine. -/
theorem neighbor_pole_displacement {x h r p : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hp : 1 ≤ p) (hr2 : r^2=x^2+h^2) :
    let w := (x:ℂ)+((p*h:ℝ):ℂ)*Complex.I
    ‖(r:ℂ)/w-((x/r:ℝ):ℂ)‖ ≤ p*(h/r) := by
  let w := (x:ℂ)+((p*h:ℝ):ℂ)*Complex.I
  have hpre : w.re = x := by simp [w,Complex.add_re,Complex.mul_I_re]
  have hpim : w.im = p*h := by simp [w,Complex.add_im,Complex.mul_I_im]
  have hp0 : 0 < p := by linarith
  have hW2 : ‖w‖^2=x^2+(p*h)^2 := by rw [Complex.sq_norm,Complex.normSq_apply,hpre,hpim];ring
  have hW : 0 < ‖w‖ := (mul_pos hp0 hh).trans_le
    ((le_abs_self _).trans (hpim ▸ Complex.abs_im_le_norm w))
  have hwr : w*(r:ℂ) ≠ 0 := mul_ne_zero (norm_pos_iff.mp hW) (by exact_mod_cast hr.ne')
  have hid : (r:ℂ)/w-((x/r:ℝ):ℂ) = (((h^2:ℝ):ℂ)-((x*p*h:ℝ):ℂ)*Complex.I)/(w*(r:ℂ)) := by
    have hcir : (r:ℂ)^2=(x:ℂ)^2+(h:ℂ)^2 := by exact_mod_cast hr2
    have hw : w ≠ 0 := norm_pos_iff.mp hW
    have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [Complex.ofReal_div,div_sub_div _ _ hw hrc]
    congr 1
    dsimp only [w]
    push_cast
    linear_combination hcir
  change ‖(r:ℂ)/w-((x/r:ℝ):ℂ)‖ ≤ _
  rw [hid,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  apply (div_le_iff₀ (mul_pos hW hr)).mpr
  have hc : p*(h/r)*(‖w‖*r) = (p*h)*‖w‖ := by
    field_simp <;> ring
  rw [hc]
  apply le_of_sq_le_sq _ (mul_nonneg (mul_pos hp0 hh).le hW.le)
  have hnum : ‖((h^2:ℝ):ℂ)-((x*p*h:ℝ):ℂ)*Complex.I‖^2 = (h^2)^2+(x*p*h)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_I_re,Complex.mul_I_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  rw [hnum,mul_pow (p*h) ‖w‖,hW2]
  have hp2 : 1 ≤ p^2 := by nlinarith [sq_nonneg (p-1)]
  have hp4 : 1 ≤ (p^2)^2 := by nlinarith [sq_nonneg (p^2-1)]
  nlinarith only [mul_le_mul_of_nonneg_right hp4 (sq_nonneg (h^2))]

#print axioms neighbor_pole_displacement
end OpenMathResearch.LongCycleExcedances
