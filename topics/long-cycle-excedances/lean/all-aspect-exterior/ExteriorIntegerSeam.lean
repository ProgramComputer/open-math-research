import FrontModulusJoin
import JoinAngle

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Angle of the first integer sample for the bounded-aspect middle gaps. -/
def exteriorIntegerSeamAngle (n : ℕ) : ℝ :=
  ((uniformJoinRank n:ℝ)+1)*π/(n:ℝ)

/-- Logarithmic modulus of the first integer sample. -/
def exteriorIntegerSeamLog (n : ℕ) : ℝ :=
  π/tan (exteriorIntegerSeamAngle n)

theorem exterior_integer_seam_geometry {n : ℕ} (hn : 10000 ≤ n) :
    0 < exteriorIntegerSeamAngle n ∧ exteriorIntegerSeamAngle n < 1/50 ∧
    6/5 < (n:ℝ)*sin (exteriorIntegerSeamAngle n)^2 ∧
    exteriorIntegerSeamLog n < (n:ℝ)/((uniformJoinRank n:ℝ)+1) := by
  let z := sqrt (n:ℝ)
  let a := (uniformJoinRank n:ℝ)+1
  let θ := exteriorIntegerSeamAngle n
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0:ℝ) < n := by linarith only [hn']
  have hz₂ : z^2 = n := sq_sqrt hn₀.le
  have hzₘ : (100:ℝ) ≤ z := by
    apply (le_sqrt (by norm_num) hn₀.le).mpr
    norm_num
    exact hn
  have hz₀ : 0 < z := by linarith only [hzₘ]
  have hfloorUpper : (uniformJoinRank n:ℝ) ≤ (7/20:ℝ)*z :=
    Nat.floor_le (by positivity)
  have ha₀ : 0 < a := by dsimp only [a]; positivity
  have ha₁ : (7/20:ℝ)*z < a := Nat.lt_floor_add_one _
  have ha₂ : a ≤ (9/25:ℝ)*z := by dsimp only [a]; linarith only [hfloorUpper,hzₘ]
  have hθpos : 0 < θ := div_pos (mul_pos ha₀ pi_pos) hn₀
  have hθz : θ*z = (a/z)*π := by
    change a*π/(n:ℝ)*z = _
    rw [←hz₂]
    field_simp [hz₀.ne'] <;> ring
  have hθz₁ : (7/20:ℝ)*π < θ*z := by
    rw [hθz]
    exact mul_lt_mul_of_pos_right ((lt_div_iff₀ hz₀).mpr ha₁) pi_pos
  have hθz₂ : θ*z ≤ (9/25:ℝ)*π := by
    rw [hθz]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hz₀).mpr ha₂) pi_pos.le
  have hθsmall : θ < 1/50 := by
    have hupper : θ*100 ≤ θ*z := mul_le_mul_of_nonneg_left hzₘ hθpos.le
    linarith only [hupper,hθz₂,pi_lt_four]
  have hθhalf : θ < π/2 := by linarith only [hθsmall,pi_gt_three]
  have hs₁ : (999/1000:ℝ)*θ < sin θ := by
    have hθsq : θ^2 ≤ (1/50:ℝ)^2 :=
      pow_le_pow_left₀ hθpos.le hθsmall.le 2
    have hθcube := mul_le_mul_of_nonneg_left hθsq hθpos.le
    have ht := sin_gt_sub_cube hθpos
    nlinarith only [ht,hθcube,hθpos]
  have hzsin : (137/125:ℝ) < sin θ*z := by
    have h := mul_lt_mul_of_pos_right hs₁ hz₀
    nlinarith only [h,hθz₁,pi_gt_d2]
  have hmid : 6/5 < (n:ℝ)*sin θ^2 := by
    have hs := pow_lt_pow_left₀ hzsin (by norm_num : (0:ℝ) ≤ 137/125) (by decide : 2 ≠ 0)
    rw [mul_pow,hz₂] at hs
    nlinarith only [hs]
  have hlog : exteriorIntegerSeamLog n < (n:ℝ)/a := by
    have ht := lt_tan hθpos hθhalf
    have htan : π/tan θ < π/θ := div_lt_div_of_pos_left pi_pos hθpos ht
    have hinv : π/θ = (n:ℝ)/a := by
      change π/(a*π/(n:ℝ)) = _
      rw [div_div_eq_mul_div]
      field_simp [ha₀.ne',pi_ne_zero] <;> ring
    exact htan.trans_eq hinv
  exact ⟨hθpos,hθsmall,hmid,hlog⟩

theorem exterior_integer_seam_log_pos {n : ℕ} (hn : 10000 ≤ n) :
    0 < exteriorIntegerSeamLog n := by
  obtain ⟨hpos,hsmall,_,_⟩ := exterior_integer_seam_geometry hn
  have hhalf : exteriorIntegerSeamAngle n < π/2 := by
    linarith only [hsmall,pi_gt_three]
  exact div_pos pi_pos (hpos.trans (lt_tan hpos hhalf))

/-- A single bound places every exterior box before either joining angle. -/
theorem exterior_cap_before_integer_seam {n : ℕ} (hn : 10000 ≤ n) :
    (459/40:ℝ)*((uniformJoinRank n:ℝ)/((uniformJoinRank n:ℝ)+1))^n <
      exp (-exteriorIntegerSeamLog n) := by
  obtain ⟨hH,hbudget⟩ := exterior_floor_budget hn
  have hs : (n:ℝ)/((uniformJoinRank n:ℝ)+1) ≤
      (n:ℝ)/((uniformJoinRank n:ℝ)+5/6) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  exact exterior_modulus_lt_phase_boundary hH hbudget
    ((exterior_integer_seam_geometry hn).2.2.2.le.trans hs) le_rfl

#print axioms exterior_integer_seam_geometry
#print axioms exterior_integer_seam_log_pos
#print axioms exterior_cap_before_integer_seam
end OpenMathResearch.LongCycleExcedances
