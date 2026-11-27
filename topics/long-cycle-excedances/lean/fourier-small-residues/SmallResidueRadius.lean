import WideOddRadius
import WideGeometry

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Enclosure on the inflated circle and middle-angle scaling imply a
Gaussian majorant in the odd pole label for the normalized radius. -/
theorem small_enclosed_radius_decay {r W p S t : ℝ} {n : ℕ}
    (hr : 0 < r) (hW : 0 < W) (hp : 1 ≤ p)
    (hgeom : (W/r)^2 = 1+(p^2-1)*S^2)
    (henc : (W/r)^2 ≤ 5/4) (hmiddle : t ≤ (n:ℝ)*S^2) :
    (r/W)^n ≤ exp (-(2/5)*t*(p^2-1)) := by
  let z := (p^2-1)*S^2
  have hp2 : 0 ≤ p^2-1 := by nlinarith [sq_nonneg (p-1)]
  have hz : 0 ≤ z := mul_nonneg hp2 (sq_nonneg _)
  have hz1 : 1+z ≤ 5/4 := by
    rw [←hgeom]
    exact henc.trans (by norm_num)
  have hpos : 0 < 1+z := by linarith
  have hlog : z/(1+z) ≤ log (1+z) := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [log_inv] at h
    have hrw : z/(1+z) = 1-(1+z)⁻¹ := by field_simp
    rw [hrw]
    linarith only [h]
  have hs : (4/5)*z ≤ log (1+z) := by
    apply le_trans _ hlog
    apply (le_div_iff₀ hpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hz1 hz]
  have hpwr := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
  have hz2 : t*(p^2-1) ≤ (n:ℝ)*z := by
    dsimp only [z]; nlinarith only [mul_le_mul_of_nonneg_left hmiddle hp2]
  have hlogr : log (1+z) = -(2*log (r/W)) := by
    rw [←hgeom,log_pow,log_div hW.ne' hr.ne',log_div hr.ne' hW.ne']
    push_cast; ring
  rw [hlogr] at hpwr
  apply (log_le_log_iff (pow_pos (div_pos hr hW) _) (exp_pos _)).mp
  rw [log_pow, log_exp]
  linarith only [hpwr,hz2]

/-- With height at most 200 and size at least 10000 the middle-angle
quantity has spare room even for the smallest included minor mode. -/
theorem small_height_middle {n : ℕ} (hn : 10000 ≤ n) {s r : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 200)
    (hr : 0 < r) (hsq : r^2 = s^2 + π^2) : 12/5 ≤ (n:ℝ)*(π/r)^2 := by
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hπ : (3.14:ℝ)^2 ≤ π^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [pi_gt_d4]) 2
  rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),hsq]
  nlinarith only [mul_le_mul_of_nonneg_right hn' (sq_nonneg π),hπ,pow_le_pow_left₀ hs hs2 2]

/-- The two height estimates both give the same exponential bound for an
enclosed positive minor pole. -/
theorem small_joint_residue_exponent {j : ℕ} (hj : 1 ≤ j) {t D : ℝ}
    (h : (t=12/5 ∧ D=9/4) ∨ (t=1 ∧ D=1/10)) :
    let p : ℝ := 2*j+1;
    -(2/5)*t*(p^2-1)+D*(p-1) ≤ -3*(j:ℝ) := by
  intro p
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hq : (j:ℝ) ≤ (j:ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj') (Nat.cast_nonneg (α := ℝ) j)]
  dsimp only [p]
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> nlinarith only [hq]

#print axioms small_enclosed_radius_decay
#print axioms small_height_middle
#print axioms small_joint_residue_exponent
end OpenMathResearch.LongCycleExcedances
