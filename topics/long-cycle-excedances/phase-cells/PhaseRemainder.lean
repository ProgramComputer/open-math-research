import SeventhMoment
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace OpenMathResearch.LongCycleExcedances
open Real

/-- After the two nearest terms are removed, the complete lattice has at
most twice the norm sum on its positive tail. Only equality of paired norms
is needed. -/
theorem two_sided_far_remainder (a : ℤ → ℂ)
    (hs : Summable fun j : ℕ => ‖a (j:ℤ)‖)
    (sym : ∀ j : ℕ, ‖a (-((j:ℤ)+1))‖ = ‖a (j:ℤ)‖) :
    ‖(∑' l : ℤ, a l) - a 0 - a (-1)‖ ≤
      2*(∑' j : ℕ, ‖a ((j+1:ℕ):ℤ)‖) := by
  have negnorm : Summable (fun j : ℕ => ‖a (-((j:ℤ)+1))‖) := by
    simpa only [sym] using hs
  have h' := hs.of_norm
  have hn := negnorm.of_norm
  have inj : Function.Injective (fun j : ℕ => j+1) := fun _ _ h => Nat.succ.inj h
  have hx := hs.comp_injective inj
  have hy := negnorm.comp_injective inj
  have ha : Summable fun j : ℕ => ‖a ((j+1:ℕ):ℤ)‖ := hx
  have hb : Summable fun j : ℕ => ‖a (-(((j+1:ℕ):ℤ)+1))‖ := hy
  rw [tsum_of_nat_of_neg_add_one h' hn, h'.tsum_eq_zero_add, hn.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, neg_one_mul]
  have hcancel (x y z w : ℂ) : x+y+(z+w)-x-z = y+w := by ring
  rw [hcancel]
  refine (norm_add_le _ _).trans ?_
  have hp := norm_tsum_le_tsum_norm ha
  have hm := norm_tsum_le_tsum_norm hb
  simp only [sym] at hm
  linarith

noncomputable def poleAngle (x : ℝ) := π/2 - Real.arctan (x/π)

theorem poleAngle_hasDerivAt (x : ℝ) :
    HasDerivAt poleAngle (-π/(x^2+π^2)) x := by
  have h := (hasDerivAt_const x (π/2)).sub ((Real.hasDerivAt_arctan (x/π)).comp x
    ((hasDerivAt_id x).div_const π))
  change HasDerivAt poleAngle (0 - 1/(1+(x/π)^2)*(1/π)) x at h
  have he : 0 - 1/(1+(x/π)^2)*(1/π) = -π/(x^2+π^2) := by
    field_simp [Real.pi_ne_zero] <;> ring
  rwa [he] at h

/-- Turning a dimensionless pole bound into an error relative to the
derivative of the principal angle. -/
theorem phase_slope_bound {n r s : ℝ} {C w : ℂ} (hn : 7 ≤ n) (hr : 0 < r)
    (hs : 0 < s) (hw : ‖w‖ = r)
    (him : (1/w).im = -s/r) (hmid : 1 ≤ n*s^2)
    (tail : ‖C-1‖ ≤ 1+8/(15*s)) :
    |((n+1)*(-s/r) - (C/w).im) + n*s/r| < (32/35)*n*s/r := by
  have hnorm := (Complex.abs_im_le_norm ((C-1)/w)).trans_eq (norm_div _ _)
  rw [hw] at hnorm
  have ha : ((C-1)/w).im = (C/w).im - (1/w).im := by rw [sub_div, Complex.sub_im]
  rw [ha, him] at hnorm
  have heq : ((n+1)*(-s/r) - (C/w).im) + n*s/r = -((C/w).im - -s/r) := by ring
  rw [heq, abs_neg]
  have hcoef := middle_derivative_error hn hs hmid
    (e := 1/s + 8/(15*s^2)) (le_of_eq (abs_of_nonneg (by positivity)))
  rw [abs_of_nonneg (by positivity)] at hcoef
  have h' : (1+8/(15*s)) / r < (32/35)*n*s/r := by
    apply (div_lt_div_iff_of_pos_right hr).2
    have he : (1/s+8/(15*s^2))*s = 1+8/(15*s) := by
      field_simp [hs.ne'] <;> ring
    simpa only [he] using mul_lt_mul_of_pos_right hcoef hs
  exact hnorm.trans_lt ((div_le_div_of_nonneg_right tail hr.le).trans_lt h')

#print axioms two_sided_far_remainder
#print axioms poleAngle_hasDerivAt
#print axioms phase_slope_bound
end OpenMathResearch.LongCycleExcedances
