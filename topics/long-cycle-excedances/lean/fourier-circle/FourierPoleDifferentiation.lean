import FourierComplexPoleBound
import FourierSquaredSum
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Complex Real Filter MeasureTheory

def squaredPoleWeight (c p : ℂ) (R : ℝ) : ℝ := ‖c‖ / poleGap p R

theorem norm_squared_pole_term (c p : ℂ) {R : ℝ} (hR : 0 < R) (hp : ‖p‖ ≠ R) (x : ℝ) :
    ‖c/(p-circleMap 0 R x)^2‖ = squaredPoleWeight c p R*(normalizedPole p R x)^2 := by
  have hg := poleGap_pos hR hp
  rw [norm_div,norm_pow]
  unfold squaredPoleWeight normalizedPole
  rw [div_pow,Real.sq_sqrt hg.le]
  field_simp [hg.ne']

theorem complexPoleKernel_angular_deriv (P c : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hp : ∀ i, ‖P i‖ ≠ R) (hfar : ∀ᶠ i in atTop, 2*R ≤ ‖P i‖)
    (hs : Summable fun i => poleWeight (c i) (P i) R)
    (hs2 : Summable fun i => squaredPoleWeight (c i) (P i) R) (x : ℝ) :
    HasDerivAt (complexPoleKernel P c R)
      (I*(circleMap 0 R x*(∑' i, c i/(P i-circleMap 0 R x)^2))) x := by
  let w := circleMap 0 R
  let a := fun i => poleWeight (c i) (P i) R
  let b := fun i => squaredPoleWeight (c i) (P i) R
  let g := fun i y => c i/(P i-w y)
  let dg := fun i y => (I*w y)*(c i/(P i-w y)^2)
  obtain ⟨M,hM,hu⟩ := normalizedPole_uniform P hR hp hfar
  have ha i : 0 ≤ a i := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb i : 0 ≤ b i := div_nonneg (norm_nonneg _) (abs_nonneg _)
  have hd (i) (y : ℝ) : HasDerivAt (g i) (dg i y) y := by
    have hne : P i-w y ≠ 0 := sub_ne_zero.mpr
      (fun h => hp i ((congrArg norm h).trans ((norm_circleMap_zero R y).trans (abs_of_pos hR))))
    have hdw := (hasDerivAt_const y (P i)).sub (hasDerivAt_circleMap 0 R y)
    exact ((hasDerivAt_const y (c i)).div hdw hne).congr_deriv (by dsimp [dg,w]; ring)
  have hr (i) y : ‖dg i y‖ ≤ R*(b i*M^2) := by
    dsimp only [dg,w]
    rw [norm_mul,norm_mul,norm_I,one_mul,norm_circleMap_zero,abs_of_pos hR,norm_squared_pole_term _ _ hR (hp i)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (normalizedPole_nonneg _ _ _) (hu i y) 2) (hb i)) hR.le
  have hbase : Summable (fun i => g i 0) := by
    apply (hs.mul_right M).of_norm_bounded
    intro i
    exact (norm_pole_term (c i) (P i) hR (hp i) 0).le.trans
      (mul_le_mul_of_nonneg_left (hu i 0) (ha i))
  have h := hasDerivAt_tsum ((hs2.mul_right (M^2)).mul_left R) hd hr hbase x
  apply h.congr_deriv
  dsimp only [dg,w]
  rw [tsum_mul_left,mul_assoc]

#print axioms norm_squared_pole_term
#print axioms complexPoleKernel_angular_deriv
end OpenMathResearch.LongCycleExcedances
