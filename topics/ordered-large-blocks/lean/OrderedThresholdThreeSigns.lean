import OrderedThresholdTwoSigns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The cancellation, quantitative sign test, and exact root count used for
ordered set partitions at threshold three. The analytic pole estimates are
hypotheses of the sign test. -/

namespace OrderedThresholdThreeSigns

open Polynomial

/-- Adding the scaled previous coefficient cancels the negative real residue.
The inputs use the cosine of the old phase and the sine of the phase increment. -/
theorem cancel_negative_real_pole
    {old next ratio oldCos oldSin shiftCos shiftSin realPole oldError nextError : ℝ}
    (hOld : old = -oldCos + realPole + oldError)
    (hNext : next = oldSin * shiftSin - oldCos * shiftCos - ratio * realPole + nextError) :
    next + ratio * old =
      oldSin * shiftSin - (shiftCos + ratio) * oldCos + (nextError + ratio * oldError) := by
  rw [hOld, hNext]
  ring

/-- The two logarithmic derivative identities and the variance bound give the
quantitative separation between the negative real pole and the principal pair. -/
theorem radius_lower_bound_from_log_derivatives
    {R rho s c₁ c₂ : ℝ} (hR : 0 < R) (hc₁ : 0 ≤ c₁)
    (hvariance : c₂ ≤ c₁ * (1 - c₁))
    (hfirst : 2 * s / rho^2 = 1 / R + (1 + c₁))
    (hsecond : 2 / rho^2 - 1 / R^2 - (2 * s / rho^2)^2 + c₂ = -2) :
    1 + R - R^2 / 2 ≤ R^2 / rho^2 := by
  rw [hfirst] at hsecond
  have hvalue : 2 / rho^2 = 1 / R^2 + (1 / R + (1 + c₁))^2 - 2 - c₂ := by
    linarith only [hsecond]
  have hexact : R^2 / rho^2 =
      1 + (1 + c₁) * R + ((1 + c₁)^2 - 2 - c₂) * R^2 / 2 := by
    calc
      R^2 / rho^2 = (2 / rho^2) * (R^2 / 2) := by ring
      _ = _ := by rw [hvalue]; field_simp [hR.ne']; ring
  have hcoef : 0 ≤ 2*c₁ + c₁^2 - c₂ := by
    nlinarith only [hc₁, hvariance, sq_nonneg c₁]
  rw [hexact]
  nlinarith only [mul_nonneg hc₁ hR.le, mul_nonneg hcoef (sq_nonneg R)]

theorem radius_lower_bound_linear
    {R rho s c₁ c₂ : ℝ} (hR : 0 < R) (hupper : R ≤ 9/5) (hc₁ : 0 ≤ c₁)
    (hvariance : c₂ ≤ c₁ * (1 - c₁))
    (hfirst : 2 * s / rho^2 = 1 / R + (1 + c₁))
    (hsecond : 2 / rho^2 - 1 / R^2 - (2 * s / rho^2)^2 + c₂ = -2) :
    1 + R/10 ≤ R^2 / rho^2 := by
  apply le_trans _ (radius_lower_bound_from_log_derivatives hR hc₁ hvariance hfirst hsecond)
  nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hupper)]

theorem radius_ratio_exp_bound {R rho : ℝ}
    (hR : 0 < R) (hupper : R ≤ 9/5) (hrho : 0 < rho)
    (hradius : 1+R/10 ≤ R^2/rho^2) :
    rho/R ≤ Real.exp (-R/24) := by
  have hExp : Real.exp (R/12) ≤ 1+R/10 := by
    apply (Real.exp_bound_div_one_sub_of_interval
      (by linarith : 0 ≤ R/12) (by linarith only [hupper] : R/12 < 1)).trans
    apply (div_le_iff₀ (by linarith only [hupper] : 0 < 1-R/12)).2
    nlinarith only [mul_nonneg hR.le (by linarith only [hupper] : 0 ≤ 2-R)]
  have hmul := (le_div_iff₀ (sq_pos_of_pos hrho)).mp hradius
  have hprod : (rho/R)^2 * (1+R/10) ≤ 1 := by
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith only [hmul]
  have hprod' : (rho/R)^2 * Real.exp (R/12) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hExp (sq_nonneg _)).trans hprod
  have hunit : (Real.exp (-R/24))^2 * Real.exp (R/12) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have heq : ((2 : ℕ) : ℝ) * (-R/24) + R/12 = 0 := by norm_num; ring
    rw [heq, Real.exp_zero]
  apply (sq_le_sq₀ (div_pos hrho hR).le (Real.exp_pos _).le).mp
  apply (mul_le_mul_right (Real.exp_pos (R/12))).mp
  exact hprod'.trans_eq hunit.symm

/-- Combining the radius ratio and the amplitude factor absorbs the real pole
into the exponentially smaller cosine budget for the analytic range. -/
theorem real_pole_envelope {N : ℕ} {R ratio B gain realPole : ℝ}
    (hN : 95 ≤ N) (hR : 0 < R) (hratio : 0 ≤ ratio)
    (hcontract : ratio ≤ Real.exp (-R/24))
    (hB : 0 ≤ B) (hGain : gain ≤ Real.exp (3*R))
    (hResidue : |realPole| = B*gain*ratio^(N+1)) :
    |realPole| ≤ B * Real.exp (-R) := by
  have hnReal : (96 : ℝ) ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast (show 96 ≤ N+1 by omega)
  have hpow : ratio^(N+1) ≤ Real.exp (-4*R) := by
    calc
      _ ≤ (Real.exp (-R/24))^(N+1) := pow_le_pow_left₀ hratio hcontract _
      _ = Real.exp (((N+1 : ℕ) : ℝ) * (-R/24)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hnReal)])
  rw [hResidue]
  calc
    B*gain*ratio^(N+1) ≤ B*(Real.exp (3*R)*Real.exp (-4*R)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hGain hpow (pow_nonneg hratio _) (Real.exp_pos _).le) hB
    _ = _ := by rw [← Real.exp_add, show 3*R + -4*R = -R by ring]

/-- The scalar dominance test at a zero of the previous row. The number B is
the sine divided by the modulus of the combined complex factor. -/
theorem signed_sine_dominates
    {sign sine cosine A C B R theta error : ℝ}
    (hsign : |sign| = 1) (hphase : sine^2 + cosine^2 = 1)
    (hband : 0 < sign * sine) (hA : 0 < A) (hC : 1/2 ≤ C)
    (hR : 0 < R) (htheta : 0 < theta)
    (hB : B = A / Real.sqrt (A^2 + C^2))
    (hlower : theta / (2*R) ≤ B) (hcos : |cosine| ≤ B * (1 - R/4))
    (herror : |error| < theta/16) :
    0 < sign * (sine*A - C*cosine + error) := by
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hB0 : 0 < B := (div_pos htheta (by positivity : 0 < 2*R)).trans_le hlower
  have hD0 : 0 < Real.sqrt (A^2 + C^2) := Real.sqrt_pos.2 (by positivity)
  have hBD : B * Real.sqrt (A^2 + C^2) = A := (eq_div_iff hD0.ne').mp hB
  have hBsq : A^2 * (1 - B^2) = C^2 * B^2 := by
    have hsq := congrArg (fun x : ℝ => x^2) hBD
    change (B * Real.sqrt (A^2 + C^2))^2 = A^2 at hsq
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ A^2 + C^2)] at hsq
    nlinarith only [hsq]
  have hcosB : |cosine| ≤ B := hcos.trans (by
    nlinarith only [mul_nonneg hB0.le hR.le])
  have hcosSq : cosine^2 ≤ B^2 := by
    rw [← sq_abs cosine]
    exact (sq_le_sq₀ (abs_nonneg cosine) hB0.le).2 hcosB
  have hunit : sign^2 = 1 := by rw [← sq_abs sign, hsign, one_pow]
  have hsinSq : 1-B^2 ≤ (sign*sine)^2 := by
    rw [mul_pow, hunit, one_mul]
    linarith only [hphase, hcosSq]
  have hmain : C*B ≤ sign * (sine*A) := by
    have hsq : (C*B)^2 ≤ (A*(sign*sine))^2 := by
      rw [mul_pow, mul_pow, ← hBsq]
      exact mul_le_mul_of_nonneg_left hsinSq (sq_nonneg A)
    have hle := (sq_le_sq₀ (mul_nonneg hC0 hB0.le) (mul_nonneg hA.le hband.le)).1 hsq
    nlinarith only [hle]
  have hcosSign : sign*cosine ≤ |cosine| := by
    simpa only [abs_mul, hsign, one_mul] using le_abs_self (sign*cosine)
  have hnegative : C*(sign*cosine) ≤ C*(B*(1-R/4)) :=
    mul_le_mul_of_nonneg_left (hcosSign.trans hcos) hC0
  have herrorSign : -(sign*error) ≤ |error| := by
    simpa only [abs_neg, abs_mul, hsign, one_mul] using le_abs_self (-(sign*error))
  have hBR : theta ≤ B*(2*R) := (div_le_iff₀ (by positivity : 0 < 2*R)).mp hlower
  have hmargin : theta/16 ≤ C*B*R/4 := by
    nlinarith only [hBR, mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hB0.le hR.le)]
  nlinarith only [hmain, hnegative, herrorSign, hmargin, herror]

theorem paired_tail_is_small
    {N : ℕ} {theta R ratio oldError nextError : ℝ}
    (hN : 4 ≤ N) (htheta : 0 < theta) (hR : 0 < R) (hupper : R ≤ 9/5)
    (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1)
    (hOld : |oldError| ≤ theta*R*(3/10)^N)
    (hNext : |nextError| ≤ theta*R*(3/10)^(N+1)) :
    |nextError + ratio*oldError| < theta/16 := by
  have hpow : (3/10 : ℝ)^N ≤ (3/10 : ℝ)^4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have hpowNext : (3/10 : ℝ)^(N+1) ≤ (3/10 : ℝ)^4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hTR : 0 ≤ theta*R := (mul_pos htheta hR).le
  have h₁ := mul_le_mul_of_nonneg_left hpow hTR
  have h₂ := mul_le_mul_of_nonneg_left hpowNext hTR
  have hRtheta := mul_le_mul_of_nonneg_left hupper htheta.le
  have hscaled : |ratio*oldError| ≤ |oldError| := by
    rw [abs_mul, abs_of_nonneg hratio]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio1 (abs_nonneg oldError)
  apply (abs_add_le _ _).trans_lt
  norm_num at h₁ h₂
  nlinarith only [hscaled, hOld, hNext, h₁, h₂, hRtheta, htheta]

/-- The separate real-pole and tail estimates give the total cosine error budget. -/
theorem cosine_error_budget
    {N : ℕ} {R theta B realPole oldError : ℝ}
    (hN : 4 ≤ N) (hR : 0 < R) (hupper : R ≤ 9/5) (htheta : 0 < theta)
    (hlower : theta/(2*R) ≤ B) (hReal : |realPole| ≤ B * Real.exp (-R))
    (hTail : |oldError| ≤ theta*R*(3/10)^N) :
    |realPole| + |oldError| ≤ B*(1-R/4) := by
  have hB0 : 0 ≤ B := (div_pos htheta (by positivity : 0 < 2*R)).le.trans hlower
  have hexp : Real.exp (-R) * (1+R) ≤ 1 := by
    calc
      _ ≤ Real.exp (-R) * Real.exp R :=
        mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp R)
          (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hexp' : Real.exp (-R) ≤ 1-R/3 := by
    apply (mul_le_mul_right (by linarith : 0 < 1+R)).mp
    apply hexp.trans
    nlinarith only [mul_nonneg hR.le (by linarith only [hupper] : 0 ≤ 2-R)]
  have hreal' : |realPole| ≤ B*(1-R/3) := hReal.trans (mul_le_mul_of_nonneg_left hexp' hB0)
  have hp : (3/10 : ℝ)^N ≤ (3/10 : ℝ)^4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have hpr : 2*R*(3/10)^N ≤ 1/12 := by
    have hprod := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*R)
    norm_num at hprod
    nlinarith only [hupper, hprod]
  have ht : theta ≤ B*(2*R) := (div_le_iff₀ (by positivity : 0 < 2*R)).mp hlower
  have htail' : |oldError| ≤ B*R/12 := by
    calc
      _ ≤ theta*R*(3/10)^N := hTail
      _ ≤ B*R*(2*R*(3/10)^N) := by
        have hmul := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ R*(3/10)^N)
        nlinarith only [hmul]
      _ ≤ B*R/12 := by
        exact (mul_le_mul_of_nonneg_left hpr (mul_nonneg hB0 hR.le)).trans_eq (by ring)
  nlinarith only [hreal', htail']

/-- The two normalized residue formulas, bounds, and old zero imply the signed
value in the next row. The negative real residue is allowed either sign. -/
theorem third_pole_next_row_sign
    {N : ℕ} {next sign phase shift B R theta ratio realPole oldError nextError : ℝ}
    (hN : 95 ≤ N) (hsign : |sign| = 1)
    (hband : 0 < sign * Real.sin phase) (hshift : 0 < Real.sin shift)
    (hcombined : 1/2 ≤ Real.cos shift + ratio)
    (hR : 0 < R) (hupper : R ≤ 9/5) (htheta : 0 < theta)
    (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1)
    (hB : B = Real.sin shift /
        Real.sqrt ((Real.sin shift)^2 + (Real.cos shift + ratio)^2))
    (hlower : theta/(2*R) ≤ B)
    (hOld : 0 = -Real.cos phase + realPole + oldError)
    (hNext : next = -Real.cos (phase + shift) - ratio*realPole + nextError)
    (hReal : |realPole| ≤ B * Real.exp (-R))
    (hTailOld : |oldError| ≤ theta*R*(3/10)^N)
    (hTailNext : |nextError| ≤ theta*R*(3/10)^(N+1)) :
    0 < sign*next := by
  have hNext' : next = Real.sin phase * Real.sin shift - Real.cos phase * Real.cos shift
      - ratio*realPole + nextError := by rw [hNext, Real.cos_add]; ring
  have hcancel := cancel_negative_real_pole hOld hNext'
  simp only [mul_zero, add_zero] at hcancel
  have hbudget := cosine_error_budget (show 4 ≤ N by omega) hR hupper htheta hlower
    hReal hTailOld
  have hcos : |Real.cos phase| ≤ B*(1-R/4) := by
    have heq : Real.cos phase = realPole + oldError := by linarith only [hOld]
    rw [heq]
    exact (abs_add_le _ _).trans hbudget
  have herr := paired_tail_is_small (show 4 ≤ N by omega) htheta hR hupper hratio hratio1
    hTailOld hTailNext
  rw [hcancel]
  exact signed_sine_dominates hsign (Real.sin_sq_add_cos_sq phase) hband hshift
    hcombined hR htheta hB hlower hcos herr

/-- The ordered threshold-three degrees and sign tests give the precise
consecutive interlacing and the whole next-row root multiset. -/
theorem threshold_three_next_row {n : ℕ} (P : ℝ[X]) (q : Fin (n / 3) → ℝ)
    (hdegree : P.natDegree = (n + 1) / 3) (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (hzero : 0 < P.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * P.eval (-q i))
    (hleading : 0 < P.leadingCoeff) :
    ∃ r : Fin ((n + 1) / 3) → ℝ, StrictMono r ∧ (∀ j, 0 < r j) ∧
      (∀ i j, j.val = i.val → r j < q i) ∧
      (∀ i j, j.val = i.val + 1 → q i < r j) ∧
      P.roots = (Finset.univ.image (fun i => -r i)).val := by
  let k := 2*(n/3) + (n%3)/2
  have hk : k/2 = n/3 := by dsimp [k]; omega
  have hk1 : (k+1)/2 = (n+1)/3 := by dsimp [k]; omega
  have hstep := @OrderedThresholdTwoSigns.threshold_two_next_row k P
  rw [hk, hk1] at hstep
  exact hstep q hdegree hq hpos hzero hs hleading

end OrderedThresholdThreeSigns
