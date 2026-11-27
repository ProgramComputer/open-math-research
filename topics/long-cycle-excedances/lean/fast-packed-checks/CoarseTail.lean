import RationalPointSound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open OpenMathResearch.LongCycleExcedances

/-- A power-of-two upper bound on the dyadic witness can already make the
ratio at most one half. This test does not require either full endpoint power. -/
theorem coarse_geometric_tail (n W s : ℕ) (y M : ℚ)
    (hy : 0 ≤ y) (hradius : y * 2^s ≤ 1)
    (hratio : 2*((W:ℚ)+2)^n ≤ 2^s*((W:ℚ)+1)^n)
    (hmargin : 2*((W:ℚ)+1)^n < M*2^(s*W)) :
    rationalTailRatio n W y < 1 ∧ rationalTailBound n W y < M := by
  let u := ((W:ℚ)+1)^n
  let v := ((W:ℚ)+2)^n
  let t : ℚ := 2^s
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have eqr : rationalTailRatio n W y = y*v/u := by
    simp only [rationalTailRatio, div_pow, u, v, mul_div_assoc]
  have h1 := mul_le_mul_of_nonneg_left hratio hy
  have h2 := mul_le_mul_of_nonneg_right hradius hu.le
  have half : rationalTailRatio n W y ≤ 1/2 := by
    rw [eqr, div_le_iff₀ hu]
    change y*(2*v) ≤ y*(t*u) at h1
    change y*t*u ≤ 1*u at h2
    linarith only [show 2*(y*v) ≤ u by
      calc
        2*(y*v) = y*(2*v) := by ring
        _ ≤ y*(t*u) := h1
        _ = y*t*u := by ring
        _ ≤ 1*u := h2
        _ = u := one_mul _]
  have hden : 0 < 1 - rationalTailRatio n W y := by linarith
  have hY : y^W * t^W ≤ 1 := by
    simpa [mul_pow, t] using pow_le_pow_left₀ (mul_nonneg hy ht.le) hradius W
  have hm : 2*u < M*t^W := by simpa only [u, t, ← pow_mul] using hmargin
  have hM : 0 < M := pos_of_mul_pos_left ((by positivity : 0 < 2*u).trans hm) (by positivity)
  have hY' := mul_le_mul_of_nonneg_left hY (by positivity : 0 ≤ 2*u)
  have upper : 2*u*y^W < M := by
    apply (lt_of_mul_lt_mul_right (a:=t^W))
    · calc
        2*u*y^W*t^W = 2*u*(y^W*t^W) := by ring
        _ ≤ 2*u*1 := hY'
        _ < M*t^W := by simpa only [mul_one] using hm
    · positivity
  refine ⟨by linarith, ?_⟩
  rw [rationalTailBound, div_lt_iff₀ hden]
  change u*y^W < M*(1-rationalTailRatio n W y)
  have less := mul_le_mul_of_nonneg_left half hM.le
  linarith [show M*(1-rationalTailRatio n W y)=M-M*rationalTailRatio n W y by ring]

#print axioms coarse_geometric_tail
end OpenMathResearch.LongCycleExcedances.IntegerSign
