import FourierAdjacentIdentity
import FourierLatticeDerivative

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real Filter MeasureTheory

private theorem circle_inv_wave (R x : ℝ) :
    (circleMap 0 R x)⁻¹ = circleWave (-1) x / (R:ℂ) := by
  have he : circleMap 0 R x = (R:ℂ)*circleWave 1 x := by
    simp [circleMap,circleWave,mul_comm]
  have hi : circleWave (1:ℤ) x * circleWave (-1) x = 1 := by
    rw [circleWave_add]
    norm_num [circleWave]
  have hinv : (circleWave 1 x)⁻¹ = circleWave (-1) x := inv_eq_of_mul_eq_one_right hi
  rw [he, mul_inv_rev, hinv, div_eq_mul_inv]

/-- Sum the signed partial fraction before taking norms. Absolute convergence
of its two separated terms justifies the addition of the infinite sums. -/
theorem circle_contrast_sum {ι : Type*} (P c : ι → ℂ) (r C : ℂ) {R : ℝ} (hR : 0 < R)
    (x : ℝ) (hp : ∀ i, P i ≠ 0) (hg : ∀ i, P i ≠ circleMap 0 R x)
    (hb : Summable (fun i => ((r/P i-C)*c i)/(P i-circleMap 0 R x)))
    (ha : Summable (fun i => (r/P i)*c i)) :
    ((r/(R:ℂ))*circleWave (-1) x-C)*(∑' i, c i/(P i-circleMap 0 R x)) =
      (∑' i, ((r/P i-C)*c i)/(P i-circleMap 0 R x)) +
      ((∑' i, (r/P i)*c i)/(R:ℂ))*circleWave (-1) x := by
  let w := circleMap 0 R x
  have hw : w ≠ 0 := by
    intro h
    have hn := norm_circleMap_zero R x
    change ‖w‖ = _ at hn
    rw [h,norm_zero,abs_of_pos hR] at hn
    linarith
  have hinv : w⁻¹ = circleWave (-1) x/(R:ℂ) := circle_inv_wave R x
  have he : ((r/(R:ℂ))*circleWave (-1) x-C) = r/w-C := by
    rw [div_eq_mul_inv r w,hinv]
    ring
  rw [he,←tsum_mul_left]
  have hterm (i : ι) : (r/w-C)*(c i/(P i-w)) =
      ((r/P i-C)*c i)/(P i-w)+((r/P i)*c i)*w⁻¹ := by
    have eq := contrast_pole_split (r:=r) (C:=C) (p:=P i) (w:=w) (hp i) hw (sub_ne_zero.mpr (hg i))
    linear_combination (norm := (simp only [div_eq_mul_inv]; ring)) c i * eq
  change (∑' i, (r/w-C)*(c i/(P i-w))) = _
  simp_rw [hterm]
  rw [hb.tsum_add (ha.mul_right w⁻¹),tsum_mul_right,hinv]
  ring

/-- On the signed odd lattice the two sums in the adjacent partial fraction
converge for the original residues at every cutoff at least three. -/
theorem odd_lattice_contrast_split (P : ℤ → ℂ)
    (hP : ∀ l, (P l).im=(2*(l:ℝ)+1)*π) (r C : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ∀ l, ‖P l‖ ≠ R) {k : ℕ} (hk : 3 ≤ k) (x : ℝ) :
    let c := fun l => (R:ℂ)^k/(P l)^(k-1)
    ((r/(R:ℂ))*circleWave (-1) x-C)*(∑' i, c i/(P i-circleMap 0 R x)) =
      (∑' i, ((r/P i-C)*c i)/(P i-circleMap 0 R x)) +
      ((∑' i, (r/P i)*c i)/(R:ℂ))*circleWave (-1) x := by
  dsimp only
  let w := circleMap 0 R x
  let c := fun l => (R:ℂ)^k/(P l)^(k-1)
  have hw : ‖w‖ = R := (norm_circleMap_zero R x).trans (abs_of_pos hR)
  have hp (l : ℤ) : P l ≠ 0 := by
    intro h
    have e := hP l
    rw [h,Complex.zero_im] at e
    have hn : (2*(l:ℝ)+1) ≠ 0 := by exact_mod_cast (show (2*l+1:ℤ) ≠ 0 by omega)
    exact (mul_ne_zero hn Real.pi_ne_zero) e.symm
  have hs : Summable (fun l => ‖c l‖) := by
    have h := (lattice_inverse_summable P hP (m:=k-1) (by omega)).mul_left (R^k)
    simpa only [c,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,
      div_eq_mul_inv,one_mul,norm_mul,norm_inv] using h
  have htail := lattice_eventually_far P hP (R:=R+1) (by linarith)
  apply circle_contrast_sum P c r C hR x hp (fun l he => hg l ((congrArg norm he).trans hw))
  · apply summable_of_cofinite_norm_le (hs.mul_left (‖r‖+‖C‖))
    filter_upwards [htail] with l hl
    have hp1 : 1 ≤ ‖P l‖ := by linarith
    have hd : 1 ≤ ‖P l-w‖ := by linarith [norm_sub_norm_le (P l) w]
    have hr : ‖r/P l‖ ≤ ‖r‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hp1
    change ‖((r/P l-C)*c l)/(P l-w)‖ ≤ _
    rw [norm_div,norm_mul]
    exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hd).trans
      (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hr le_rfl)) (norm_nonneg _))
  · apply summable_of_cofinite_norm_le (hs.mul_left ‖r‖)
    filter_upwards [htail] with l hl
    rw [norm_mul,norm_div]
    exact mul_le_mul_of_nonneg_right (div_le_self (norm_nonneg _) (by linarith)) (norm_nonneg _)

#print axioms odd_lattice_contrast_split
#print axioms circle_contrast_sum
end OpenMathResearch.LongCycleExcedances
