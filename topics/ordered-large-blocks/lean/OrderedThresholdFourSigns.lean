import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! The two-pair determinant identity and next-row sign estimate at ordered
threshold four. The analytic estimates for the determinant and the tails
are inputs to the signed transfer. -/

namespace OrderedThresholdFourSigns

open scoped ComplexConjugate

noncomputable def turn (x : ℝ) : ℂ := Complex.exp ((x : ℂ)*Complex.I)

noncomputable def oldFactor (A alpha : ℝ) : ℂ :=
  1 + (A : ℂ)*turn alpha

noncomputable def nextFactor (A ratio alpha delta phi : ℝ) : ℂ :=
  turn phi*(1 + Complex.I*(A : ℂ)*(ratio : ℂ)*turn (alpha+delta))

def determinant (U V : ℂ) : ℝ := (V*conj U).im

private theorem re_turn_mul (phase : ℝ) (W : ℂ) :
    (turn phase*W).re = Real.cos phase*W.re - Real.sin phase*W.im := by
  rw [Complex.mul_re]
  simp only [turn, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

private theorem determinant_coordinates (U V : ℂ) :
    determinant U V = U.re*V.im - V.re*U.im := by
  simp only [determinant, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Eliminating the old cosine term produces the determinant of the two
complex factors. The identity includes both residual terms with their signs. -/
theorem determinant_identity
    {phase oldError nextError next : ℝ} {U V : ℂ}
    (hOld : (turn phase*U).re = oldError)
    (hNext : next = -(turn phase*V).re + nextError) :
    U.re*next = Real.sin phase*determinant U V + U.re*nextError - V.re*oldError := by
  rw [re_turn_mul] at hOld hNext
  rw [hNext, determinant_coordinates, ← hOld]
  ring

/-- The quantitative zero-gap lower bound leaves more than half the squared
gap after the phase perturbation. -/
theorem determinant_margin_after_perturbation
    {gap sine cosine base actual A : ℝ}
    (hgap : gap = 1-A) (hA : A < 1)
    (hcos : 7/10 ≤ cosine)
    (hangle : cosine*(A+(47/50)*gap) ≤ sine)
    (hbase : gap*(sine-A*cosine) ≤ base)
    (hperturbation : |actual-base| ≤ (132/1000)*gap^2) :
    gap^2/2 < actual := by
  have hg : 0 < gap := by linarith only [hgap, hA]
  have hsize : cosine*(47/50)*gap ≤ sine-A*cosine := by
    nlinarith only [hangle]
  have hbase' := (mul_le_mul_of_nonneg_left hsize hg.le).trans hbase
  have hcos' := mul_le_mul_of_nonneg_right hcos
    (by positivity : 0 ≤ (47/50 : ℝ)*gap^2)
  nlinarith only [hbase', hcos', (abs_le.mp hperturbation).1, sq_pos_of_pos hg]

private theorem factor_bounds
    {A ratio alpha delta phi : ℝ} (hA₀ : 0 ≤ A) (hA₁ : A < 1)
    (hr₀ : 0 ≤ ratio) (hr₁ : ratio ≤ 1) :
    0 < (oldFactor A alpha).re ∧
      |(oldFactor A alpha).re| ≤ 2 ∧
      |(nextFactor A ratio alpha delta phi).re| ≤ 2 := by
  have hU : (oldFactor A alpha).re = 1 + A*Real.cos alpha := by
    simp [oldFactor, turn, Complex.add_re, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  have hcos : -(1 : ℝ) ≤ Real.cos alpha := Real.neg_one_le_cos _
  have hpos : 0 < (oldFactor A alpha).re := by
    rw [hU]
    nlinarith only [hA₁, mul_nonneg hA₀ (sub_nonneg.mpr hcos)]
  have hturn (x : ℝ) : ‖turn x‖ = 1 := Complex.norm_exp_ofReal_mul_I x
  have hV : ‖nextFactor A ratio alpha delta phi‖ ≤ 2 := by
    unfold nextFactor
    rw [norm_mul, hturn, one_mul]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.I*(A : ℂ)*(ratio : ℂ)*turn (alpha+delta)‖ := norm_add_le _ _
      _ = 1 + A*ratio := by
        simp only [norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hA₀, abs_of_nonneg hr₀, hturn, one_mul, mul_one]
      _ ≤ _ := by nlinarith only [hA₁, mul_nonneg hA₀ (sub_nonneg.mpr hr₁)]
  refine ⟨hpos, ?_, (Complex.abs_re_le_norm _).trans hV⟩
  rw [abs_of_pos hpos, hU]
  nlinarith only [hA₁, mul_nonneg hA₀ (sub_nonneg.mpr (Real.cos_le_one alpha))]

/-- The determinant lower bound and the explicit residual allowance preserve
the phase-band sign of the next coefficient. -/
theorem determinant_sign_transfer
    {phase sign gap oldError nextError next : ℝ} {U V : ℂ}
    (hgap : 0 < gap) (hsign : |sign| = 1) (hsin : 1/4 < sign*Real.sin phase)
    (hU : 0 < U.re) (hUabs : |U.re| ≤ 2) (hVabs : |V.re| ≤ 2)
    (hdet : gap^2/2 < determinant U V)
    (herrOld : |oldError| ≤ gap^2/100) (herrNext : |nextError| ≤ gap^2/100)
    (hOld : (turn phase*U).re = oldError)
    (hNext : next = -(turn phase*V).re + nextError) :
    0 < sign*next := by
  have hdet0 : 0 < determinant U V := (by positivity : 0 < gap^2/2).trans hdet
  have hmain : gap^2/8 < (sign*Real.sin phase)*determinant U V := by
    calc
      gap^2/8 = (1/4)*(gap^2/2) := by ring
      _ < (1/4)*determinant U V := mul_lt_mul_of_pos_left hdet (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right hsin hdet0
  have habsNext : |sign*(U.re*nextError)| ≤ gap^2/50 := by
    rw [abs_mul, hsign, one_mul, abs_mul]
    exact (mul_le_mul hUabs herrNext (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have habsOld : |sign*(V.re*oldError)| ≤ gap^2/50 := by
    rw [abs_mul, hsign, one_mul, abs_mul]
    exact (mul_le_mul hVabs herrOld (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hEq := congrArg (fun x : ℝ => sign*x) (determinant_identity hOld hNext)
  have hprod : 0 < U.re*(sign*next) := by
    change sign*(U.re*next) =
      sign*(Real.sin phase*determinant U V + U.re*nextError - V.re*oldError) at hEq
    nlinarith only [hmain, (abs_le.mp habsNext).1, (abs_le.mp habsOld).2, hEq, sq_nonneg gap]
  exact pos_of_mul_pos_right hprod hU.le

/-- The signed transfer for the actual two-pair factors used at threshold
four, with a residual tolerance of (1-A)^2/100 in each row. -/
theorem threshold_four_two_pair_sign
    {A ratio alpha delta phi phase sign oldError nextError next : ℝ}
    (hA₀ : 0 ≤ A) (hA₁ : A < 1) (hr₀ : 0 ≤ ratio) (hr₁ : ratio ≤ 1)
    (hsign : |sign| = 1) (hsin : 1/4 < sign*Real.sin phase)
    (hdet : (1-A)^2/2 < determinant (oldFactor A alpha) (nextFactor A ratio alpha delta phi))
    (herrOld : |oldError| ≤ (1-A)^2/100) (herrNext : |nextError| ≤ (1-A)^2/100)
    (hOld : (turn phase*oldFactor A alpha).re = oldError)
    (hNext : next = -(turn phase*nextFactor A ratio alpha delta phi).re + nextError) :
    0 < sign*next := by
  obtain ⟨hU, hUabs, hVabs⟩ := factor_bounds (alpha := alpha) (delta := delta) (phi := phi)
    hA₀ hA₁ hr₀ hr₁
  exact determinant_sign_transfer (sub_pos.mpr hA₁) hsign hsin hU hUabs hVabs
    hdet herrOld herrNext hOld hNext

end OrderedThresholdFourSigns
