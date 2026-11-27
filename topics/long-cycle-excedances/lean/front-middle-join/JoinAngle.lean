import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

def uniformJoinRank (n : ℕ) : ℕ :=
  ⌊(7/20:ℝ)*√(n:ℝ)⌋₊

def uniformJoinAngle (n : ℕ) : ℝ :=
  ((uniformJoinRank n:ℝ)+5/6)*π/(n:ℝ)

/-- The logarithmic modulus at the exterior/middle junction, π cot θ. -/
def uniformJoinLog (n : ℕ) : ℝ :=
  π/tan (uniformJoinAngle n)

theorem uniform_join_geometry {n : ℕ} (hn : 10^4 ≤ n) :
    0 < uniformJoinAngle n ∧ uniformJoinAngle n < 1/50 ∧
      1 < (n:ℝ)*sin (uniformJoinAngle n)^2 ∧
      2*√(n:ℝ) < uniformJoinLog n ∧
      uniformJoinLog n < (n:ℝ)/((uniformJoinRank n:ℝ)+5/6) := by
  let z := √(n:ℝ)
  let a := (uniformJoinRank n:ℝ)+5/6
  let θ := uniformJoinAngle n
  have hn' : (10^4:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0:ℝ) < n := by linarith
  have hz₂ : z^2 = n := sq_sqrt hn₀.le
  have hzₘ : (100:ℝ) ≤ z := by
    apply (Real.le_sqrt (by norm_num) hn₀.le).mpr
    norm_num at hn' ⊢
    exact hn'
  have hz₀ : 0 < z := by linarith
  have ha₀ : 0 < a := by dsimp only [a]; positivity
  have hfloorUpper : (uniformJoinRank n:ℝ) ≤ (7/20:ℝ)*z :=
    Nat.floor_le (by positivity)
  have hfloorLower : (7/20:ℝ)*z < (uniformJoinRank n:ℝ)+1 :=
    Nat.lt_floor_add_one _
  have ha₁ : (17/50:ℝ)*z < a := by dsimp only [a]; linarith
  have ha₂ : a ≤ (9/25:ℝ)*z := by dsimp only [a]; linarith
  have hθpos : 0 < θ := div_pos (mul_pos ha₀ pi_pos) hn₀
  have hθz : θ*z = (a/z)*π := by
    change a*π/(n:ℝ)*z = _
    rw [← hz₂]
    field_simp [hz₀.ne']; ring
  have hθz₁ : (17/50:ℝ)*π < θ*z := by
    rw [hθz]
    exact mul_lt_mul_of_pos_right ((lt_div_iff₀ hz₀).mpr ha₁) pi_pos
  have hθz₂ : θ*z ≤ (9/25:ℝ)*π := by
    rw [hθz]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hz₀).mpr ha₂) pi_pos.le
  have hθsmall : θ < 1/50 := by
    have hupper : θ*100 ≤ θ*z := mul_le_mul_of_nonneg_left hzₘ hθpos.le
    linarith only [hupper, hθz₂, pi_lt_four]
  have hθhalf : θ < π/2 := by linarith only [hθsmall, pi_gt_three]
  have hs₀ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθpos (by linarith)
  have hs₁ : (99/100:ℝ)*θ < sin θ := by
    have hθsq : θ^2 ≤ (1/50:ℝ)^2 :=
      pow_le_pow_left₀ hθpos.le hθsmall.le 2
    have hθcube := mul_le_mul_of_nonneg_left hθsq hθpos.le
    have ht := sin_gt_sub_cube hθpos
    nlinarith only [ht, hθcube, hθpos]
  have hzsin : 1 < sin θ*z := by
    have h := mul_lt_mul_of_pos_right hs₁ hz₀
    nlinarith only [h, hθz₁, pi_gt_three]
  have hmid : 1 < (n:ℝ)*sin θ^2 := by
    have hpositive : 0 < sin θ*z+1 := by linarith only [hzsin]
    have h : (1:ℝ)^2 < (sin θ*z)^2 := by
      nlinarith only [mul_pos (sub_pos.mpr hzsin) hpositive]
    rw [mul_pow,hz₂] at h
    nlinarith only [h]
  have hcos : (99/100:ℝ) < cos θ := by
    have hθsq := pow_le_pow_left₀ hθpos.le hθsmall.le 2
    linarith only [hθsq, one_sub_sq_div_two_le_cos (x := θ)]
  have hlog : 2*z < uniformJoinLog n := by
    have hsin := mul_le_mul_of_nonneg_right (sin_le hθpos.le) hz₀.le
    have hc := mul_lt_mul_of_pos_left hcos pi_pos
    have h : 2*z*sin θ < π*cos θ := by
      nlinarith only [hsin,hθz₂,hc,pi_pos]
    change 2*z < π/tan θ
    rw [tan_eq_sin_div_cos,div_div_eq_mul_div]
    exact (lt_div_iff₀ hs₀).mpr h
  have hxUpper : uniformJoinLog n < (n:ℝ)/a := by
    have ht := lt_tan hθpos hθhalf
    have htan : π/tan θ < π/θ := div_lt_div_of_pos_left pi_pos hθpos ht
    have hinv : π/θ = (n:ℝ)/a := by
      change π/(a*π/(n:ℝ)) = _
      rw [div_div_eq_mul_div]
      field_simp [ha₀.ne', pi_ne_zero]; ring
    rw [← hinv]
    exact htan
  exact ⟨hθpos,hθsmall,hmid,hlog,hxUpper⟩

/-- The cutoff inequality in the uniform short-cycle argument yields a much
stronger size separation than the junction uses. -/
theorem uniform_join_cutoff_separation {n k : ℕ} (hn : 10^4 ≤ n) (hk : 0 < k)
    (hcut : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    10*√(k:ℝ) < uniformJoinLog n := by
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hk₀ : (0:ℝ) < k := by exact_mod_cast hk
  have h := (lt_div_iff₀ (show 0 < 200*(k:ℝ) by positivity)).mp
    ((show (20:ℝ) ≤ 30*log (n:ℝ)+20 by linarith only [log_nonneg hn₁]).trans_lt hcut)
  have hk25 : 25*(k:ℝ) < n := by linarith only [h,hk₀]
  have hs : √(25*(k:ℝ)) < √(n:ℝ) := sqrt_lt_sqrt (by positivity) hk25
  have h25 : √(25:ℝ) = 5 := by
    rw [show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 25),h25] at hs
  exact (by linarith only [hs] : 10*√(k:ℝ) < 2*√(n:ℝ)).trans (uniform_join_geometry hn).2.2.2.1

theorem arctan_uniform_join {n : ℕ} (hn : 10^4 ≤ n) :
    arctan (uniformJoinLog n/π) = π/2-uniformJoinAngle n := by
  obtain ⟨hpos,hsmall,_,_,_⟩ := uniform_join_geometry hn
  have hhalf : uniformJoinAngle n < π/2 := by linarith only [hsmall,pi_gt_three]
  have ht : 0 < tan (uniformJoinAngle n) := hpos.trans (lt_tan hpos hhalf)
  have he : uniformJoinLog n/π = tan (π/2-uniformJoinAngle n) := by
    rw [uniformJoinLog,tan_pi_div_two_sub]
    field_simp [pi_ne_zero,ht.ne']; ring
  rw [he,arctan_tan (by linarith only [hhalf,pi_pos]) (by linarith only [hpos])]

theorem uniform_join_radius_sq {n : ℕ} (hn : 10^4 ≤ n) :
    (uniformJoinLog n)^2+π^2 < (n:ℝ)*π^2 := by
  let θ := uniformJoinAngle n
  let b := uniformJoinLog n
  obtain ⟨hpos,hsmall,hmid,_,_⟩ := uniform_join_geometry hn
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hpos (by linarith only [hsmall,pi_gt_three])
  have hx : b*sin θ = π*cos θ := by
    change (π/tan θ)*sin θ = _
    rw [tan_eq_sin_div_cos,div_div_eq_mul_div,div_mul_cancel₀ _ hs.ne']
  have he : (b^2+π^2)*sin θ^2 = π^2 := calc
    _ = (b*sin θ)^2+(π*sin θ)^2 := by ring
    _ = π^2 := by
      rw [hx,mul_pow,mul_pow,←mul_add,cos_sq_add_sin_sq,mul_one]
  have hRight : π^2 < ((n:ℝ)*π^2)*sin θ^2 := calc
    _ < π^2*((n:ℝ)*sin θ^2) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hmid (pow_pos pi_pos 2)
    _ = _ := by ring
  change b^2+π^2 < _
  by_contra! h
  have hle := mul_le_mul_of_nonneg_right h (sq_nonneg (sin θ))
  rw [he] at hle
  exact (not_lt_of_ge hle) hRight

theorem uniform_join_phase_from_imag {n : ℕ} (hn : 10^4 ≤ n) {γ : ℝ}
    (hγ : |γ| < 12/25) :
    ((n:ℝ)+1)*uniformJoinAngle n-γ < ((uniformJoinRank n:ℝ)+1)*π := by
  have hθ := (uniform_join_geometry hn).2.1
  have hn₀ : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (n:ℝ)*uniformJoinAngle n = ((uniformJoinRank n:ℝ)+5/6)*π := by
    unfold uniformJoinAngle
    rw [mul_comm,div_mul_cancel₀ _ hn₀]
  nlinarith only [he,hθ,(abs_lt.mp hγ).1,pi_gt_three]

#print axioms uniform_join_geometry
#print axioms uniform_join_cutoff_separation
#print axioms arctan_uniform_join
#print axioms uniform_join_radius_sq
#print axioms uniform_join_phase_from_imag
end OpenMathResearch.LongCycleExcedances
