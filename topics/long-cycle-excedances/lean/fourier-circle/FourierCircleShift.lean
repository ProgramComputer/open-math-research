import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real MeasureTheory
open scoped Interval

def circleWave (j : ℤ) (x : ℝ) : ℂ := Complex.exp ((j:ℂ)*Complex.I*(x:ℂ))

def normalizedFourierIntegral (f : ℝ → ℂ) (j : ℤ) : ℂ :=
  (∫ x in (0:ℝ)..2*π, circleWave (-j) x*f x)/(2*(π:ℂ))

theorem circleWave_deriv (j : ℤ) (x : ℝ) :
    HasDerivAt (circleWave j) ((j:ℂ)*Complex.I*circleWave j x) x := by
  have h := (((hasDerivAt_id (x:ℂ)).const_mul ((j:ℂ)*Complex.I)).cexp).comp_ofReal
  change HasDerivAt (fun y : ℝ => Complex.exp ((j:ℂ)*Complex.I*(y:ℂ))) _ x
  simpa only [circleWave,id_eq,mul_one,one_mul,mul_comm ((j:ℂ)*Complex.I)] using h

theorem circleWave_continuous (j : ℤ) : Continuous (circleWave j) :=
  continuous_iff_continuousAt.mpr (fun x => (circleWave_deriv j x).continuousAt)

theorem circleWave_zero (j : ℤ) : circleWave j 0=1 := by simp [circleWave]

theorem circleWave_period (j : ℤ) : circleWave j (2*π)=1 := by
  unfold circleWave
  push_cast
  rw [show (j:ℂ)*Complex.I*(2*(π:ℂ))=(j:ℂ)*(2*(π:ℂ)*Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I j

theorem circleWave_add (a b : ℤ) (x : ℝ) :
    circleWave a x*circleWave b x = circleWave (a+b) x := by
  unfold circleWave
  rw [←Complex.exp_add]
  push_cast
  congr 1
  ring

/-- A periodic derivative with frequency shift gives an exact identity on
every Fourier coefficient, including frequency zero. -/
theorem shifted_periodic_derivative {f g : ℝ → ℂ} (k j : ℤ)
    (hper : f (2*π)=f 0) (hg : Continuous g)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*g x) x) :
    (j:ℂ)*normalizedFourierIntegral f j = normalizedFourierIntegral g (j-k) := by
  let H (x:ℝ) := circleWave (-j) x*f x
  let F (x:ℝ) := circleWave (-j) x*f x
  let G (x:ℝ) := circleWave (-(j-k)) x*g x
  have fc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cF : Continuous F := (circleWave_continuous _).mul fc
  have cG : Continuous G := (circleWave_continuous _).mul hg
  have diff (x:ℝ) : HasDerivAt H (Complex.I*(G x-(j:ℂ)*F x)) x := by
    apply ((circleWave_deriv (-j) x).mul (hf x)).congr_deriv
    dsimp only [F,G]
    rw [show -(j-k) = -j+k by omega, ←circleWave_add]
    push_cast
    ring
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=2*π) (fun x _ => diff x)
    ((continuous_const.mul (cG.sub (continuous_const.mul cF))).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (cG.intervalIntegrable _ _) ((continuous_const.mul cF).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at ht
  have endpt : H (2*π) - H 0=0 := by simp [H,circleWave_period,circleWave_zero,hper]
  rw [endpt] at ht
  have he := sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left Complex.I_ne_zero)
  unfold normalizedFourierIntegral
  rw [←mul_div_assoc]
  exact congrArg (fun z : ℂ => z/(2*(π:ℂ))) he.symm

#print axioms shifted_periodic_derivative
end OpenMathResearch.LongCycleExcedances
