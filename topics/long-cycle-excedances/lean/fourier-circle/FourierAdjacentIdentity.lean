import FourierCircleContrast
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Partial fraction for the common circle.  Its second term shifts the
Fourier frequency by exactly one. -/
theorem contrast_pole_split {r C w p : ℂ} (hp : p≠0) (hw : w≠0) (hgap : p-w≠0) :
    (r/w-C)/(p-w)=(r/p-C)/(p-w)+(r/p)/w := by
  field_simp [hp,hw,hgap]
  ring

/-- The signed adjacent coefficient identity after two integrations by parts.
B is the kernel weighted by r/p-C.  The sum of the off-kernel residues is A;
on the radius R, the second partial fraction contributes A times wave(-1). -/
theorem fourier_adjacent_twice {f D B E : ℝ→ℂ} (n k : ℤ) (a C A : ℂ)
    (hf0 : f (2*π)=f 0) (hb0 : B (2*π)=B 0) (hD : Continuous D) (hE : Continuous E)
    (hf : ∀ x, HasDerivAt f (Complex.I*circleWave k x*(f x*D x)) x)
    (hB : ∀ x, HasDerivAt B (Complex.I*E x) x)
    (hsplit : ∀ x, (a*circleWave (-1) x-C)*D x=B x+A*circleWave (-1) x) :
    ((n-k:ℤ):ℂ)*(n:ℂ)*(a*normalizedFourierIntegral f (n+1)-C*normalizedFourierIntegral f n) =
      normalizedFourierIntegral (fun x => f x*(circleWave k x*D x*B x+E x)) (n-k)
      +((n-k:ℤ):ℂ)*A*normalizedFourierIntegral f (n+1-k)
      -((n-k:ℤ):ℂ)*a*normalizedFourierIntegral f (n+1) := by
  let d := fun x => f x*D x
  let b := fun x => f x*B x
  let w := circleWave (-1)
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cb := continuous_iff_continuousAt.mpr (fun x => (hB x).continuousAt)
  have cd : Continuous d := cf.mul hD
  have cw : Continuous w := circleWave_continuous _
  have hrow (j : ℤ) := shifted_periodic_derivative (f:=f) (g:=d) k j hf0 cd hf
  have hid : (fun x => a*(w x*d x)+(-C)*d x) =
      (fun x => 1*b x+A*(w x*f x)) := by
    funext x
    have h := congrArg (fun y : ℂ => f x*y) (hsplit x)
    dsimp only [b,d,w]
    try dsimp only at h
    linear_combination h
  have h := congrArg (fun g : ℝ→ℂ => normalizedFourierIntegral g (n-k)) hid
  try dsimp only at h
  rw [fourier_linear_pair (f := fun x => w x*d x) (g := d) (cw.mul cd) cd,
    fourier_linear_pair (f := b) (g := fun x => w x*f x) (cf.mul cb) (cw.mul cf), one_mul] at h
  dsimp only [w] at h
  rw [fourier_modulation,fourier_modulation,show n-k-(-1) = n+1-k by omega,
    ←hrow (n+1),←hrow n] at h
  have h₂ := fourier_kernel_second k (n-k) hf0 hb0 hD hE hf hB
  change ((n-k:ℤ):ℂ)*normalizedFourierIntegral b (n-k) = _ at h₂
  push_cast at h
  linear_combination ((n-k:ℤ):ℂ)*h+h₂

#print axioms contrast_pole_split
#print axioms fourier_adjacent_twice
end OpenMathResearch.LongCycleExcedances
