import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false
namespace OpenMathResearch.LongCycleExcedances
open Polynomial Finset

noncomputable def momentOf (A : ℕ → ℝ[X]) (m : ℕ) (t : ℝ) : ℝ :=
  t * (A m).eval t / (1 - t)^(m+1)

/-- The Eulerian insertion recurrence differentiates a logistic moment. -/
theorem momentOf_hasDerivAt (A : ℕ → ℝ[X]) (m : ℕ) (t : ℝ) (ht : t < 1)
    (recurrence : A (m+1) = (1 + C (m : ℝ) * X) * A m +
      X * (1-X) * derivative (A m)) :
    HasDerivAt (momentOf A m) ((A (m+1)).eval t / (1-t)^(m+2)) t := by
  have hden : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hd := ((hasDerivAt_id t).mul ((A m).hasDerivAt t)).div
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow (m+1))
    (pow_ne_zero _ hden)
  convert hd using 1 <;> try rfl'
  rw [recurrence]
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, eval_sub, id_eq, Pi.sub_apply,
    Pi.pow_apply, Nat.succ_sub_one, Pi.mul_apply, zero_sub, mul_one, one_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp [hden]
  ring

noncomputable def logarithmCoeff (A : ℕ → ℝ[X]) (m : ℕ) (x : ℝ) : ℝ :=
  -momentOf A m (-Real.exp (-x)) / (m+1).factorial

theorem logarithmCoeff_hasDerivAt (A : ℕ → ℝ[X]) (m : ℕ) (x : ℝ)
    (recurrence : A (m+1) = (1 + C (m : ℝ) * X) * A m +
      X * (1-X) * derivative (A m)) :
    HasDerivAt (logarithmCoeff A m) (-((m:ℝ)+2) * logarithmCoeff A (m+1) x) x := by
  let t := -Real.exp (-x)
  have ht : t < 1 := by dsimp [t]; linarith [Real.exp_pos (-x)]
  have hp : HasDerivAt (fun u : ℝ => -Real.exp (-u)) (-t) x := by
    convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).neg using 1 <;> first | rfl' | simp [t, Function.comp_def]
  have hh := (((momentOf_hasDerivAt A m t ht recurrence).comp x hp).neg).div_const
    ((m+1).factorial:ℝ)
  convert hh using 1 <;> try rfl'
  dsimp only [logarithmCoeff, momentOf, Function.comp_apply, t]
  rw [Nat.factorial_succ (m+1)]
  push_cast
  field_simp
  ring

/-- Differentiate the finite log tilt along a translated pole. All interior
coefficient derivatives cancel against the derivative of the next power. -/
theorem finiteTilt_diagonal_hasDerivAt (g : ℕ → ℝ → ℝ) (m : ℕ) (x : ℝ) (b : ℂ)
    (hg : ∀ j, HasDerivAt (g j) (-((j:ℝ)+2) * g (j+1) x) x) :
    HasDerivAt (fun u : ℝ => ∑ j ∈ range m, (g j u : ℂ) * ((u:ℂ)+b)^(j+1))
      ((g 0 x : ℂ) - ((m:ℂ)+1) * g m x * ((x:ℂ)+b)^m) x := by
  induction m with
  | zero => simpa using (hasDerivAt_const x (0 : ℂ))
  | succ m ih =>
    have hw : HasDerivAt (fun u : ℂ => u+b) 1 (x:ℂ) := (hasDerivAt_id _).add_const b
    have hh := ih.add ((hg m).ofReal_comp.mul (hw.pow (m+1)).comp_ofReal)
    simp only [sum_range_succ]
    convert hh using 1 <;> try rfl'
    push_cast
    try simp only [Pi.pow_apply, Nat.succ_sub_one, one_mul, mul_one, smul_eq_mul]
    ring

#print axioms finiteTilt_diagonal_hasDerivAt
#print axioms logarithmCoeff_hasDerivAt
end OpenMathResearch.LongCycleExcedances
