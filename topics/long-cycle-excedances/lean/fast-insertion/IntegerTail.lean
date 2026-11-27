import RationalPointSound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open OpenMathResearch.LongCycleExcedances

/-- Clear the strictly positive geometric-tail denominator before evaluating
integer powers. The extra factor D also covers a retained width of zero. -/
theorem integer_tail_margin (n W D : ℕ) (p M : ℤ) (hd : 0 < D)
    (hz : 0 < (D : ℤ)*((W : ℤ)+1)^n - p*((W : ℤ)+2)^n)
    (hm : (D : ℤ)*(((W : ℤ)+1)^n)^2*p^W <
      M*(D : ℤ)^W*((D : ℤ)*((W : ℤ)+1)^n-p*((W : ℤ)+2)^n)) :
    rationalTailRatio n W ((p : ℚ)/D) < 1 ∧
      rationalTailBound n W ((p : ℚ)/D) < (M : ℚ) := by
  let u : ℚ := ((W : ℚ)+1)^n
  let v : ℚ := ((W : ℚ)+2)^n
  have hD : (0 : ℚ) < D := by exact_mod_cast hd
  have hu : 0 < u := by dsimp [u]; positivity
  have hZ : (0 : ℚ) < D*u - p*v := by dsimp [u,v]; exact_mod_cast hz
  have hM : (D : ℚ)*u^2*(p : ℚ)^W < M*(D : ℚ)^W*(D*u-p*v) := by
    dsimp [u,v]; exact_mod_cast hm
  have eqR : rationalTailRatio n W ((p : ℚ)/D) = p*v/(D*u) := by
    simp only [rationalTailRatio, div_pow, u, v, div_mul_div_comm]
  have hDU := mul_pos hD hu
  have hr : p*v/(D*u) < 1 := (div_lt_iff₀ hDU).mpr (by linarith)
  refine ⟨eqR.trans_lt hr, ?_⟩
  rw [rationalTailBound, eqR, div_lt_iff₀ (sub_pos.mpr hr)]
  change u * ((p : ℚ) / D)^W < M * (1-p*v/(D*u))
  rw [div_pow, mul_div_assoc', one_sub_div hDU.ne', mul_div_assoc']
  rw [div_lt_div_iff₀ (pow_pos hD W) hDU]
  calc
    u * (p : ℚ)^W * (D * u) = (D : ℚ)*u^2*(p : ℚ)^W := by ring
    _ < _ := hM
    _ = _ := by ring

#print axioms integer_tail_margin
end OpenMathResearch.LongCycleExcedances.IntegerSign
