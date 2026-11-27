import AllCutoffMesh
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

def complexPoissonTerm (m : ℕ) (z : ℂ) := Complex.exp (-z)*z^m/(m.factorial:ℂ)
def cutoffExp (m : ℕ) (z : ℂ) :=
  Complex.exp (-z)*(∑ j ∈ range (m+1), z^j/(j.factorial:ℂ))

private theorem complexPoissonTerm_succ_deriv (m : ℕ) (z : ℂ) :
    HasDerivAt (complexPoissonTerm (m+1)) (complexPoissonTerm m z-complexPoissonTerm (m+1) z) z := by
  have he : HasDerivAt (fun y : ℂ => Complex.exp (-y)) (-Complex.exp (-z)) z := by
    simpa only [Function.comp_def,mul_neg,mul_one] using
      (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg
  have hd := (he.mul ((hasDerivAt_id z).pow (m+1))).div_const ((m+1).factorial:ℂ)
  change HasDerivAt (complexPoissonTerm (m+1))
    ((-Complex.exp (-z)*z^(m+1)+Complex.exp (-z)*((m+1:ℕ)*(z^(m+1-1))*1))/(m+1).factorial) z at hd
  convert hd using 1
  unfold complexPoissonTerm
  rw [Nat.factorial_succ]; push_cast
  simp only [Nat.add_sub_cancel,mul_one]
  have hfac : (m.factorial:ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hm : (m:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hfac,hm] <;> ring

theorem cutoffExp_deriv (m : ℕ) (z : ℂ) :
    HasDerivAt (cutoffExp m) (-complexPoissonTerm m z) z := by
  induction m with
  | zero =>
    have eq0 : cutoffExp 0 = fun y : ℂ => Complex.exp (-y) := by
      funext y; simp [cutoffExp]
    rw [eq0]
    simpa [complexPoissonTerm,Function.comp_def] using
      (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg
  | succ m ih =>
    have h := ih.add (complexPoissonTerm_succ_deriv m z)
    have he : cutoffExp (m+1) = fun y => cutoffExp m y+complexPoissonTerm (m+1) y := by
      funext y
      unfold cutoffExp complexPoissonTerm
      rw [sum_range_succ]
      ring
    rw [he]
    convert h using 1
    ring

def verticalArgument (x v : ℝ) : ℂ := (x:ℂ)+(v:ℂ)*Complex.I
def verticalMode (m a : ℕ) (x v : ℝ) := cutoffExp m ((a:ℂ)*verticalArgument x v)/(a:ℂ)

private theorem verticalMode_deriv (m a : ℕ) (ha : 0 < a) (x v : ℝ) :
    HasDerivAt (verticalMode m a x) (-Complex.I*complexPoissonTerm m ((a:ℂ)*verticalArgument x v)) v := by
  let Z (u : ℂ) := (a:ℂ)*((x:ℂ)+u*Complex.I)
  have hz : HasDerivAt Z ((a:ℂ)*Complex.I) (v:ℂ) := by
    simpa only [Z,one_mul] using (((hasDerivAt_id (v:ℂ)).mul_const Complex.I).const_add (x:ℂ)).const_mul (a:ℂ)
  have H := (((cutoffExp_deriv m (Z (v:ℂ))).comp (v:ℂ) hz).div_const (a:ℂ)).comp_ofReal
  have heq : (-complexPoissonTerm m (Z (v:ℂ)) * ((a:ℂ)*Complex.I))/(a:ℂ) =
      -Complex.I*complexPoissonTerm m ((a:ℂ)*verticalArgument x v) := by
    dsimp [Z,verticalArgument]
    field_simp [show (a:ℂ) ≠ 0 by exact_mod_cast ha.ne'] <;> ring
  rw [←heq]
  exact H

/-- Each vertical mode has an explicit Lipschitz bound supplied by one positive
real Poisson mass, with no derivative of an infinite sum. -/
theorem vertical_mode_transport (m a : ℕ) (ha : 0 < a) {x l u C : ℝ}
    (hx : 0 ≤ x) (hlu : l ≤ u)
    (hrad : ∀ v ∈ Set.Icc l u, ‖verticalArgument x v‖^m ≤ x^m*C) :
    ‖verticalMode m a x u-verticalMode m a x l‖ ≤ C*poissonTerm m ((a:ℝ)*x)*(u-l) := by
  let D (v : ℝ) := -Complex.I*complexPoissonTerm m ((a:ℂ)*verticalArgument x v)
  have hb (v : ℝ) (hv : v ∈ Set.Icc l u) : ‖D v‖ ≤ C*poissonTerm m ((a:ℝ)*x) := by
    have hre : (-((a:ℂ)*verticalArgument x v)).re = -((a:ℝ)*x) := by
      simp [verticalArgument,Complex.mul_re,Complex.add_re,Complex.mul_I_re]
    unfold D complexPoissonTerm poissonTerm
    simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,norm_div,norm_pow,Complex.norm_exp,hre,
      Complex.norm_natCast,mul_pow]
    convert mul_le_mul_of_nonneg_left (hrad v hv)
      (show 0 ≤ Real.exp (-((a:ℝ)*x))*(a:ℝ)^m/(m.factorial:ℝ) by positivity) using 1 <;> ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_ : v ∈ Set.Icc l u) => (verticalMode_deriv m a ha x v).hasDerivWithinAt)
    hb (convex_Icc l u) (Set.left_mem_Icc.mpr hlu) (Set.right_mem_Icc.mpr hlu)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hlu)] using h

#print axioms cutoffExp_deriv
#print axioms vertical_mode_transport
end OpenMathResearch.LongCycleExcedances
