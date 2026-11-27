import BernsteinProbability
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Normalize a supplied atom estimate at the binomial mode. -/
theorem binomial_peak_from_scaled_bound {n d : ℕ} (hd : 0 < d) (half : 2*d ≤ n)
    (h : 2*√(d:ℝ)*√((n-d:ℕ):ℝ)*binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ √(n:ℝ)) :
    binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ 1/√(d:ℝ) := by
  have hsub : d < n := by omega
  have ha : 0 < √(d:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hb : 0 < 2*√((n-d:ℕ):ℝ) :=
    mul_pos (by norm_num) (sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hsub)))
  have hr : (n:ℝ) ≤ 4*((n-d:ℕ):ℝ) := by
    rw [Nat.cast_sub hsub.le]
    have hcast : (2:ℝ)*d ≤ n := by exact_mod_cast half
    linarith
  have hs := sqrt_le_sqrt hr
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show √(4:ℝ) = 2 by rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]] at hs
  apply (le_div_iff₀ ha).mpr
  apply le_of_mul_le_mul_left _ hb
  calc
    _ = 2*√(d:ℝ)*√((n-d:ℕ):ℝ)*binomialDensity n d ((d:ℝ)/(n:ℝ)) := by ring
    _ ≤ √(n:ℝ) := h
    _ ≤ 2*√((n-d:ℕ):ℝ) * 1 := by rw [mul_one]; exact hs

/-- Specialize the supplying weighted-product atom to the exact mode.
This is only algebraic transport of the supplied estimate. -/
theorem binomial_peak_from_uniform_atom {n d : ℕ} (hd : 0 < d) (half : 2*d ≤ n)
    (atom : ∀ {A B N : ℕ}, 0 < A → 0 < B → A+B=N → ∀ {u v : ℝ}, 0 < u → 0 < v →
      2*√(A:ℝ)*√(B:ℝ)*(N.choose A:ℝ)*(u^A*v^B) ≤ √(N:ℝ)*(u+v)^N) :
    binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ 1/√(d:ℝ) := by
  have hlt : d < n := by omega
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let u := (d:ℝ)/(n:ℝ)
  let v := 1-u
  have hu : 0 < u := div_pos (Nat.cast_pos.mpr hd) hn
  have hv : 0 < v := sub_pos.mpr ((div_lt_one hn).mpr (Nat.cast_lt.mpr hlt))
  have hunit : u+v = 1 := by dsimp [v]; ring
  have h := atom hd (Nat.sub_pos_of_lt hlt) (show d+(n-d)=n by omega) hu hv
  rw [hunit, one_pow, mul_one] at h
  apply binomial_peak_from_scaled_bound hd half
  unfold binomialDensity
  calc
    _ = 2*√(d:ℝ)*√((n-d:ℕ):ℝ)*(n.choose d:ℝ)*(u^d*v^(n-d)) := by
      dsimp [u,v]
      ring
    _ ≤ _ := h

#print axioms binomial_peak_from_scaled_bound
#print axioms binomial_peak_from_uniform_atom
end OpenMathResearch.LongCycleExcedances
