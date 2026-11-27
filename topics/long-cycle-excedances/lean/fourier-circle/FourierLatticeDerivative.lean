import FourierOddPoleProduct
import FourierDerivativeBound

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory Filter

/-- On either integer tail the squared-kernel weight is eventually bounded
by the ordinary weight, uniformly in the choice of residues. -/
theorem lattice_squared_weights (P d : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R : ℝ} (hR : 0 < R)
    (hs : Summable (fun l => poleWeight (d l) (P l) R)) :
    Summable (fun l => squaredPoleWeight (d l) (P l) R) := by
  apply Summable.of_norm_bounded_eventually _ hs
  filter_upwards [lattice_eventually_far P hP (R := R+1) (by linarith)] with l hl
  have hpos : 0 ≤ ‖P l‖^2-R^2 := by
    nlinarith [sq_nonneg (‖P l‖-R), mul_nonneg (by linarith : 0 ≤ ‖P l‖-R-1)
      (by linarith : 0 ≤ ‖P l‖+R+1)]
  have hg : 1 ≤ poleGap (P l) R := by
    rw [poleGap,abs_of_nonneg hpos]
    nlinarith [mul_nonneg (by linarith : 0 ≤ ‖P l‖-R-1) (by linarith : 0 ≤ ‖P l‖+R+1)]
  have hroot : 1 ≤ √(poleGap (P l) R) := by
    apply Real.le_sqrt_of_sq_le
    simpa using hg
  have hcomp : √(poleGap (P l) R) ≤ poleGap (P l) R := by
    nlinarith [Real.sq_sqrt (le_trans zero_le_one hg),
      mul_nonneg (by linarith : 0 ≤ √(poleGap (P l) R)-1) (Real.sqrt_nonneg (poleGap (P l) R))]
  rw [Real.norm_eq_abs, squaredPoleWeight, poleWeight, abs_of_nonneg (div_nonneg (norm_nonneg _) (le_trans zero_le_one hg))]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hcomp

set_option maxHeartbeats 1800000 in
/-- Full signed-lattice angular mass bound, with a contrast multiplier on
each residue. The right side retains each exact squared pole gap. -/
theorem odd_lattice_contrast_derivative (P t : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R S : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) (ht : ∀ l : ℤ, ‖t l‖ ≤ |2*(l:ℝ)+1| * S)
    {k : ℕ} (hk : 3 ≤ k) :
    let c := fun l => (R:ℂ)^k/(P l)^(k-1)
    let d := fun l => t l*c l
    (∫ x in (0:ℝ)..2*π, ‖deriv (fun y : ℝ => ∑' l, d l/(P l-circleMap 0 R y)) x‖) ≤
      R*((∑' l, squaredPoleWeight (d l) (P l) R)*(2*π)) := by
  dsimp only
  let c := fun l => (R:ℂ)^k/(P l)^(k-1)
  let d := fun l => t l*c l
  let a := fun l => poleWeight (c l) (P l) R
  have ha l : 0 ≤ a l := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hs : Summable (fun l => poleWeight (d l) (P l) R) := by
    apply Summable.of_nonneg_of_le (fun l => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) _
      ((lattice_moment_weights P hP hR hk).2.mul_right S)
    intro l
    have he : poleWeight (d l) (P l) R = ‖t l‖ * a l := by
      dsimp [d,a,poleWeight]
      rw [norm_mul]
      ring
    change poleWeight (d l) (P l) R ≤ (|2*(l:ℝ)+1| * a l)*S
    rw [he]
    exact (mul_le_mul_of_nonneg_right (ht l) (ha l)).trans_eq (by ring)
  let e := Equiv.intEquivNat.symm
  have he : Tendsto e atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact e.injective.tendsto_cofinite
  have hfar := he.eventually (lattice_eventually_far P hP hR)
  have hb := complexPoleKernel_derivative_bound (P ∘ e) (d ∘ e) hR (fun i => hg _) hfar
    (e.summable_iff.mpr hs) (e.summable_iff.mpr (lattice_squared_weights P d hP hR hs))
  have hfun : complexPoleKernel (P ∘ e) (d ∘ e) R =
      fun y : ℝ => ∑' l, d l/(P l-circleMap 0 R y) := by
    funext y
    exact e.tsum_eq (fun l => d l/(P l-circleMap 0 R y))
  rw [hfun] at hb
  exact hb.trans_eq (by rw [← e.tsum_eq (fun l => squaredPoleWeight (d l) (P l) R)]; rfl)

/-- The integrated contrast derivative has the paper's factor S times the
first odd-height moment of the squared pole weights. -/
theorem odd_lattice_contrast_first_moment (P t : ℤ → ℂ)
    (hP : ∀ l, (P l).im = (2*(l:ℝ)+1)*π) {R S : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) (ht : ∀ l : ℤ, ‖t l‖ ≤ |2*(l:ℝ)+1| * S)
    {k : ℕ} (hk : 3 ≤ k) :
    let c := fun l => (R:ℂ)^k/(P l)^(k-1)
    (∫ x in (0:ℝ)..2*π, ‖deriv (fun y : ℝ =>
      ∑' l, (t l*c l)/(P l-circleMap 0 R y)) x‖) ≤
      R*((∑' l : ℤ, |2*(l:ℝ)+1| * squaredPoleWeight (c l) (P l) R)*S*(2*π)) := by
  dsimp only
  let c := fun l => (R:ℂ)^k/(P l)^(k-1)
  let m := fun l : ℤ => 2*(l:ℝ)+1
  let b := fun l => squaredPoleWeight (c l) (P l) R
  have hb l : 0 ≤ b l := div_nonneg (norm_nonneg _) (abs_nonneg _)
  have hs' : Summable (fun l => poleWeight ((m l:ℂ)*c l) (P l) R) := by
    have hs := (lattice_moment_weights P hP hR hk).2
    simpa only [poleWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_div_assoc,m,c] using hs
  have hs : Summable (fun l => |m l| * b l) := by
    have hs := lattice_squared_weights P (fun l => (m l:ℂ)*c l) hP hR hs'
    simpa only [squaredPoleWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_div_assoc,b] using hs
  have hle l : squaredPoleWeight (t l*c l) (P l) R ≤ (|m l| * b l)*S := by
    change ‖t l*c l‖ / poleGap (P l) R ≤ _
    rw [norm_mul,mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right (ht l) (hb l)).trans_eq (by dsimp [m]; ring)
  have hsum := Summable.of_nonneg_of_le
    (fun l => div_nonneg (norm_nonneg (t l*c l)) (abs_nonneg _)) hle (hs.mul_right S)
  have he := hsum.tsum_le_tsum hle (hs.mul_right S)
  rw [tsum_mul_right] at he
  have h := odd_lattice_contrast_derivative P t hP hR hg ht hk
  exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he Real.two_pi_pos.le) hR.le)

#print axioms odd_lattice_contrast_first_moment
#print axioms lattice_squared_weights
#print axioms odd_lattice_contrast_derivative
end OpenMathResearch.LongCycleExcedances
