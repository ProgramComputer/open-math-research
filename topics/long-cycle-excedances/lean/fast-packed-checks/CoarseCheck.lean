import CoarseTail
import CompactPoint

namespace OpenMathResearch.LongCycleExcedances.IntegerSign
open OpenMathResearch.LongCycleExcedances

/-- The cheaper power-of-two bound implies the same strict integer comparison
as the exact geometric-tail branch, so both branches certify the same sign. -/
theorem coarse_integer_margin (n W D level : ℕ) (p M : ℤ) (hd : 0 < D) (hp : 0 ≤ p)
    (rad : p * 2^level ≤ (D:ℤ))
    (ratio : 2*((W:ℤ)+2)^n ≤ 2^level*((W:ℤ)+1)^n)
    (margin : 2*((W:ℤ)+1)^n < M*2^(level*W)) :
    0 < (D:ℤ)*((W:ℤ)+1)^n-p*((W:ℤ)+2)^n ∧
    (D:ℤ)*(((W:ℤ)+1)^n)^2*p^W <
      M*(D:ℤ)^W*((D:ℤ)*((W:ℤ)+1)^n-p*((W:ℤ)+2)^n) := by
  let u := ((W:ℚ)+1)^n
  let v := ((W:ℚ)+2)^n
  have hD : (0:ℚ) < D := by exact_mod_cast hd
  have hu : 0 < u := by dsimp [u]; positivity
  have hr : (p:ℚ)/D * 2^level ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hD]
    exact_mod_cast rad
  obtain ⟨hq,hm⟩ := coarse_geometric_tail n W level ((p:ℚ)/D) (M:ℚ)
    (div_nonneg (by exact_mod_cast hp) hD.le) hr (by exact_mod_cast ratio) (by exact_mod_cast margin)
  have eqR : rationalTailRatio n W ((p:ℚ)/D) = p*v/(D*u) := by
    simp only [rationalTailRatio, div_pow, u, v, div_mul_div_comm]
  rw [eqR] at hq
  have hdu := mul_pos hD hu
  have hz : 0 < D*u-p*v := by
    have hh := (div_lt_one hdu).mp hq
    linarith
  have hzi : 0 < (D:ℤ)*((W:ℤ)+1)^n-p*((W:ℤ)+2)^n := by
    dsimp only [u,v] at hz
    exact_mod_cast hz
  refine ⟨hzi, ?_⟩
  rw [rationalTailBound, eqR, div_lt_iff₀ (sub_pos.mpr hq)] at hm
  change u*((p:ℚ)/D)^W < M*(1-(p:ℚ)*v/(D*u)) at hm
  rw [div_pow, mul_div_assoc', one_sub_div hdu.ne', mul_div_assoc',
    div_lt_div_iff₀ (pow_pos hD W) hdu] at hm
  have back : (D:ℚ)*u^2*p^W < M*(D:ℚ)^W*(D*u-p*v) := by
    calc
      _ = u*(p:ℚ)^W*(D*u) := by ring
      _ < _ := hm
      _ = _ := by ring
  dsimp only [u,v] at back
  exact_mod_cast back

def coarsePointCheck (n w level : ℕ) (c : ℕ → ℤ) (p : ℤ) (D : ℕ) (s : ℤ) : Bool :=
  let cs := firstCoeffs c w
  let M := s*roundedRatio p D cs-2-uncertainty p D cs
  let U := ((w:ℤ)+1)^n
  let V := ((w:ℤ)+2)^n
  decide (0<D ∧ 0≤p ∧ 2*p≤(D:ℤ) ∧ (s=1 ∨ s= -1) ∧
    p*2^level≤(D:ℤ) ∧ 2*V≤2^level*U ∧ 2*U<M*2^(level*w))

theorem packed_check_of_coarse (n w level : ℕ) (c : ℕ → ℤ) (p : ℤ) (D : ℕ) (s : ℤ)
    (ok : coarsePointCheck n w level c p D s = true) : packedPointCheck n w c p D s = true := by
  unfold coarsePointCheck at ok
  obtain ⟨hd,hp,hpD,hs,rad,ratio,margin⟩ := of_decide_eq_true ok
  obtain ⟨hz,hm⟩ := coarse_integer_margin n w D level p _ hd hp rad ratio margin
  unfold packedPointCheck
  exact decide_eq_true ⟨hd,hp,hpD,hs,hz,hm⟩

#print axioms coarse_integer_margin
#print axioms packed_check_of_coarse
end OpenMathResearch.LongCycleExcedances.IntegerSign
