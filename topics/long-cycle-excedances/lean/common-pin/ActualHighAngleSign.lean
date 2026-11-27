import HighAngleRowEstimate
import HighAngleScalar
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped Real
open Finset LongCycles OpenMathResearch.LongCycleExcedances
namespace RepositoryQuotientAudit

/-- Modulus of the evaluated cutoff tilt at the principal pole. -/
def highAngleAmplitude (k : ℕ) (x : ℝ) : ℝ :=
  ‖seriesValue (coherentTilt k (-Real.exp (-x))) (coherentPole x 0)‖

theorem highAngleAmplitude_pos {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    0 < highAngleAmplitude k x := by
  unfold highAngleAmplitude
  rw [seriesValue_original_coherentTilt hk, Complex.norm_exp]
  exact Real.exp_pos _

/-- For each qualifying degree the normalized original row is within one
sixth of the real part of the corresponding normalized principal mode. -/
theorem actual_high_angle_normalized_error {n k : ℕ} (hn : 0 < n) (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x) (hangle : ‖coherentPole x 0‖ ≤ 2*π)
    (hsize : 100*(k:ℝ)*Real.log k ≤ n) (q : ℕ) (hnq : n ≤ q) :
    |highAngleRow q k x / highAngleAmplitude k x -
      (highAnglePrincipal q k x).re / highAngleAmplitude k x| ≤ 1/6 := by
  let t := -Real.exp (-x)
  let w := coherentPole x 0
  let r := ‖w‖
  let R := highAngleRadius x k
  let ξ := (1 + 1/(k:ℝ))⁻¹
  let B := 5 + 18*Real.log k
  let A := Real.exp B
  let M := highAngleAmplitude k x
  have hk' : (7:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ) := by positivity
  have hr : 0 < r := coherentPole_near_pos x
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξ1 : ξ ≤ 1 := by
    change (1 + 1/(k:ℝ))⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ (by have := one_div_pos.mpr hk0; linarith)
  have hre : r/R = ξ := by
    change r / (r*(1+1/(k:ℝ))) = _
    rw [div_mul_eq_div_div, div_self hr.ne', one_div]
  have hA : 0 < A := Real.exp_pos _
  have hRM : ‖w‖ ≤ R := by
    change r ≤ r*(1+1/(k:ℝ))
    nlinarith [mul_pos hr (one_div_pos.mpr hk0)]
  have hM' : A⁻¹ ≤ M := by
    have hb := actual_high_angle_log_mass hk hx hangle
    have ha := norm_seriesValue_coherentTilt_ge (by omega : 2 ≤ k) t w R hRM
    rw [← Real.exp_neg]
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans ha
  have hM : 0 < M := (inv_pos.mpr hA).trans_le hM'
  have hiM : M⁻¹ ≤ A := by
    simpa using (inv_le_inv₀ hM (inv_pos.mpr hA)).2 hM'
  have hA2 : A^2 = Real.exp 10 * (k:ℝ)^36 := by
    dsimp only [A,B]
    rw [← Real.exp_nat_mul]
    norm_num
    rw [show 2*(5+18*Real.log (k:ℝ)) = 10+36*Real.log (k:ℝ) by ring,
      Real.exp_add, ← show ((36:ℕ):ℝ) = 36 by norm_num, Real.exp_nat_mul, Real.exp_log hk0]
  have hq : 0 < q := hn.trans_le hnq
  have hb := actual_high_angle_row_error hq hk hx hangle
  dsimp only at hb
  change |highAngleRow q k x - (highAnglePrincipal q k x).re| ≤
    A*(((k:ℝ)+1)*(r/R)^q + 10*(r/R)^(q-1) + 4*(r/R)^q) at hb
  rw [hre] at hb
  have hd := pow_le_pow_of_le_one hξ.le hξ1 (show n-1 ≤ q by omega)
  have hd' := pow_le_pow_of_le_one hξ.le hξ1 (show n-1 ≤ q-1 by omega)
  have h₁ : ((k:ℝ)+1)*ξ^q + 10*ξ^(q-1) + 4*ξ^q ≤ 4*(k:ℝ)*ξ^(n-1) := by
    have h := mul_le_mul_of_nonneg_right (show (k:ℝ)+15 ≤ 4*(k:ℝ) by linarith) (pow_nonneg hξ.le (n-1))
    have h' := mul_le_mul_of_nonneg_left hd (show 0 ≤ (k:ℝ)+1 by positivity)
    nlinarith only [hd, hd', h, h']
  rw [← sub_div, abs_div, abs_of_pos hM, div_eq_mul_inv]
  have hgeo := high_angle_geometric_envelope (k:ℝ) n hk' hn
    (Real.exp_one_lt_d9.trans (by norm_num)) hsize
  apply le_of_lt
  calc
    _ ≤ (A*(4*(k:ℝ)*ξ^(n-1)))*A := by
      apply mul_le_mul (hb.trans (mul_le_mul_of_nonneg_left h₁ hA.le)) hiM
        (inv_nonneg.mpr hM.le) (by positivity)
    _ = 4*Real.exp 10*(k:ℝ)^37*ξ^(n-1) := by
      rw [show A*(4*(k:ℝ)*ξ^(n-1))*A = 4*(k:ℝ)*ξ^(n-1)*A^2 by ring, hA2]
      ring
    _ < _ := hgeo

/-- At every qualifying zero of the literal old row, the literal next row
has the sign of the imaginary part of the same principal pole mode. -/
theorem original_high_angle_next_sign {n k : ℕ} (hn : 0 < n) (hk : 7 ≤ k)
    {x : ℝ} (hx : 0 ≤ x) (hangle : ‖coherentPole x 0‖ ≤ 2*π)
    (hsize : 100*(k:ℝ)*Real.log k ≤ n)
    (hold : (enumerator n k).eval (-Real.exp (-x)) = 0) :
    0 < (enumerator (n+1) k).eval (-Real.exp (-x)) * (highAnglePrincipal n k x).im := by
  let t := -Real.exp (-x)
  let w := coherentPole x 0
  let r := ‖w‖
  let M := highAngleAmplitude k x
  let z := highAngleUnit x
  let a := highAnglePrincipal n k x / (M : ℂ)
  have hr : 0 < r := coherentPole_near_pos x
  have hM : 0 < M := highAngleAmplitude_pos (by omega) x
  have hz : ‖z‖ = 1 := by
    dsimp [z, highAngleUnit]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hpa (q : ℕ) : ‖highAnglePrincipal q k x‖ = M := by
    unfold highAnglePrincipal
    rw [norm_mul, norm_pow, hz, one_pow, mul_one]
    rfl
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [norm_div, hpa, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, div_self hM.ne']
  have herror := actual_high_angle_normalized_error hn hk hx hangle hsize
  have hz_im : z.im = -π/r := by
    have he : w.normSq = r^2 := (Complex.sq_norm w).symm
    change (((r:ℝ):ℂ)/w).im = _
    rw [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub, he]
    change _ = _
    rw [show w.im = π by simpa [w] using coherentPole_im x 0]
    field_simp [hr.ne'] <;> ring
  have hS : (1:ℝ)/2 ≤ -z.im := by
    rw [hz_im, neg_div, neg_neg]
    apply (le_div_iff₀ hr).2
    linarith
  have hc : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans_eq hz
  have hre_div (q : ℕ) :
      (highAnglePrincipal q k x / (M:ℂ)).re = (highAnglePrincipal q k x).re / M := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, ← div_eq_mul_inv]
  have him_div :
      a.im = (highAnglePrincipal n k x).im / M := by
    dsimp only [a]
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, ← div_eq_mul_inv]
  have hnextmode : highAnglePrincipal (n+1) k x / (M:ℂ) = a*z := by
    dsimp only [a, z, highAnglePrincipal]
    rw [show n+1+1 = (n+1)+1 by rfl, pow_succ]
    ring
  have hnow : |a.re| ≤ 1/6 := by
    obtain h := herror n le_rfl
    rw [← hre_div, show highAngleRow n k x = 0 by simp [highAngleRow, hold],
      zero_div, zero_sub, abs_neg] at h
    exact h
  have hnext : |highAngleRow (n+1) k x / M - (highAnglePrincipal (n+1) k x).re / M| ≤ 1/6 :=
    herror (n+1) (Nat.le_succ n)
  rw [← hre_div, hnextmode, Complex.mul_re] at hnext
  have hsign := next_sign_of_unit_principal_mode ha hc hS hnow
    (show |highAngleRow (n+1) k x/M - (z.re*a.re+(-z.im)*a.im)| ≤ 1/6 by
      rw [show z.re*a.re+(-z.im)*a.im = a.re*z.re-a.im*z.im by ring]
      exact hnext)
  rw [him_div] at hsign
  have ht : 0 < 1-t := by dsimp [t]; linarith [Real.exp_pos (-x)]
  let C := (r^(n+1+1)/2)/((1-t)^(n+1+1)*(n+1).factorial)
  have hC : 0 < C := by dsimp [C]; positivity
  have hprod : 0 < (C/(M*M)) *
      ((enumerator (n+1) k).eval t * (highAnglePrincipal n k x).im) := by
    have he : (C/(M*M)) *
        ((enumerator (n+1) k).eval t * (highAnglePrincipal n k x).im) =
        (highAngleRow (n+1) k x / M) * ((highAnglePrincipal n k x).im / M) := by
      change _ = (r^(n+1+1)/2 *
        ((enumerator (n+1) k).eval t / ((1-t)^(n+1+1)*(n+1).factorial)) / M) *
        ((highAnglePrincipal n k x).im / M)
      unfold C
      ring
    rwa [he]
  exact pos_of_mul_pos_right hprod (div_nonneg hC.le (mul_pos hM hM).le)

#print axioms actual_high_angle_normalized_error
#print axioms original_high_angle_next_sign
end RepositoryQuotientAudit
