import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Set Finset Polynomial
open scoped Polynomial

/-- Real binomial mass at trial count n, outcome d, and probability t. -/
def binomialDensity (n d : ℕ) (t : ℝ) : ℝ :=
  (n.choose d : ℝ) * t^d * (1-t)^(n-d)

theorem binomialDensity_nonneg (n d : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ binomialDensity n d t := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hs : 0 ≤ 1-t := sub_nonneg.mpr ht1
  unfold binomialDensity
  positivity

private def bernsteinPrefix (n d : ℕ) : ℝ[X] :=
  ∑ i ∈ range (d+1), bernsteinPolynomial ℝ (n+1) i

private theorem derivative_bernsteinPrefix (n d : ℕ) :
    (bernsteinPrefix n d).derivative =
      -((n+1 : ℕ) : ℝ[X]) * bernsteinPolynomial ℝ n d := by
  induction d with
  | zero => simpa [bernsteinPrefix] using bernsteinPolynomial.derivative_zero ℝ (n+1)
  | succ d ih =>
    unfold bernsteinPrefix at *
    rw [sum_range_succ, Polynomial.derivative_add, ih, bernsteinPolynomial.derivative_succ]
    simp only [Nat.add_sub_cancel]
    ring

private theorem bernsteinPrefix_at_zero (n d : ℕ) : (bernsteinPrefix n d).eval 0 = 1 := by
  unfold bernsteinPrefix
  rw [Polynomial.eval_finsetSum]
  refine (sum_eq_single_of_mem 0 (mem_range.mpr (by omega)) ?_).trans ?_
  · intro i _ hi
    simp [bernsteinPolynomial.eval_at_0, hi]
  · simp [bernsteinPolynomial.eval_at_0]

private theorem bernsteinPrefix_at_one {n d : ℕ} (hd : d ≤ n) :
    (bernsteinPrefix n d).eval 1 = 0 := by
  unfold bernsteinPrefix
  rw [Polynomial.eval_finsetSum]
  apply sum_eq_zero
  intro i hi
  have hne : i ≠ n+1 := by have := mem_range.mp hi; omega
  simp [bernsteinPolynomial.eval_at_1, hne]

/-- The negative prefix divided by n+1 is an antiderivative of one binomial mass. -/
def binomialPrimitive (n d : ℕ) (t : ℝ) : ℝ :=
  (bernsteinPrefix n d).eval t / (-((n:ℝ)+1))

theorem hasDerivAt_binomialPrimitive (n d : ℕ) (t : ℝ) :
    HasDerivAt (binomialPrimitive n d) (binomialDensity n d t) t := by
  have hf := ((bernsteinPrefix n d).hasDerivAt t).div_const (-((n:ℝ)+1))
  have hne : -((n:ℝ)+1) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have he : (bernsteinPrefix n d).derivative.eval t / (-((n:ℝ)+1)) =
      binomialDensity n d t := by
    rw [derivative_bernsteinPrefix]
    simp only [eval_mul, eval_neg, eval_add, eval_one, eval_natCast, Nat.cast_add, Nat.cast_one]
    rw [mul_div_cancel_left₀ _ hne]
    simp [bernsteinPolynomial, binomialDensity]
  rw [he] at hf
  exact hf

theorem binomialPrimitive_mass {n d : ℕ} (hd : d ≤ n) :
    binomialPrimitive n d 1 - binomialPrimitive n d 0 = 1 / ((n:ℝ)+1) := by
  unfold binomialPrimitive
  rw [bernsteinPrefix_at_zero, bernsteinPrefix_at_one hd]
  rw [zero_div, zero_sub, div_neg, neg_neg]

private theorem hasDerivAt_binomialDensity_succ (a b : ℕ) (t : ℝ) :
    HasDerivAt (binomialDensity (a+b+2) (a+1))
      (((a+b+2).choose (a+1):ℝ) * (t^a * (1-t)^b) *
        ((a:ℝ)+1-((a:ℝ)+(b:ℝ)+2)*t)) t := by
  have hd : a+b+2-(a+1) = b+1 := by omega
  have hp := (hasDerivAt_id t).pow (a+1)
  have hq := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow (b+1)
  have hpq := (hp.mul hq).const_mul (((a+b+2).choose (a+1):ℝ))
  let c : ℝ := ((a+b+2).choose (a+1) : ℝ)
  change HasDerivAt (fun y : ℝ => c*(y^(a+1)*(1-y)^(b+1)))
    (c*((↑(a+1:ℕ)*t^(a+1-1)*1)*(1-t)^(b+1) +
      t^(a+1)*(↑(b+1:ℕ)*(1-t)^(b+1-1)*(0-1)))) t at hpq
  have hf : (fun y : ℝ => c*(y^(a+1)*(1-y)^(b+1))) =
      binomialDensity (a+b+2) (a+1) := by
    funext y
    unfold binomialDensity
    rw [hd]
    exact (mul_assoc c _ _).symm
  have he :
      c*((↑(a+1:ℕ)*t^(a+1-1)*1)*(1-t)^(b+1) +
        t^(a+1)*(↑(b+1:ℕ)*(1-t)^(b+1-1)*(0-1))) =
      c*(t^a*(1-t)^b)*((a:ℝ)+1-((a:ℝ)+(b:ℝ)+2)*t) := by
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, zero_sub]
    rw [pow_succ t a, pow_succ (1-t) b]
    ring
  rw [hf, he] at hpq
  exact hpq

/-- Unimodality on the closed unit interval, including degenerate grid spacing. -/
theorem binomialDensity_unimodal {n d : ℕ} (hd : 0 < d) (hnd : d < n) :
    let m := (d:ℝ)/(n:ℝ)
    m ∈ Icc (0:ℝ) 1 ∧ MonotoneOn (binomialDensity n d) (Icc 0 m) ∧
      AntitoneOn (binomialDensity n d) (Icc m 1) := by
  let a := d-1
  let b := n-d-1
  have he : d = a+1 := by dsimp [a]; omega
  have hn : n = a+b+2 := by dsimp [a,b]; omega
  rw [hn,he]
  dsimp only
  let m := ((a+1:ℕ):ℝ)/((a+b+2:ℕ):ℝ)
  change m ∈ Icc (0:ℝ) 1 ∧ MonotoneOn _ (Icc 0 m) ∧ AntitoneOn _ (Icc m 1)
  have hden : (0:ℝ) < ((a+b+2:ℕ):ℝ) := by positivity
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm1 : m ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [one_mul, Nat.cast_le] using (show a+1 ≤ a+b+2 by omega)
  refine ⟨⟨hm0,hm1⟩, ?_, ?_⟩
  · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hasDerivAt_binomialDensity_succ a b t).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_binomialDensity_succ a b t).differentiableAt.differentiableWithinAt
    · intro t ht
      have hmem := interior_subset ht
      have ht0 : 0 ≤ t := (mem_Icc.mp hmem).1
      have ht1 : t ≤ 1 := (mem_Icc.mp hmem).2.trans hm1
      have hleft := (le_div_iff₀ hden).mp (mem_Icc.mp hmem).2
      have htSub : 0 ≤ 1-t := sub_nonneg.mpr ht1
      rw [(hasDerivAt_binomialDensity_succ a b t).deriv]
      have hlin : 0 ≤ (a:ℝ)+1-((a:ℝ)+(b:ℝ)+2)*t := by push_cast at hleft; nlinarith
      exact mul_nonneg (by positivity) hlin
  · apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun t ht => (hasDerivAt_binomialDensity_succ a b t).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_binomialDensity_succ a b t).differentiableAt.differentiableWithinAt
    · intro t ht
      have hmem := interior_subset ht
      have ht0 : 0 ≤ t := hm0.trans (mem_Icc.mp hmem).1
      have ht1 : t ≤ 1 := (mem_Icc.mp hmem).2
      have hright := (div_le_iff₀ hden).mp (mem_Icc.mp hmem).1
      have htSub : 0 ≤ 1-t := sub_nonneg.mpr ht1
      rw [(hasDerivAt_binomialDensity_succ a b t).deriv]
      have hlin : (a:ℝ)+1-((a:ℝ)+(b:ℝ)+2)*t ≤ 0 := by push_cast at hright; nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlin

#print axioms hasDerivAt_binomialPrimitive
#print axioms binomialPrimitive_mass
#print axioms binomialDensity_unimodal
end OpenMathResearch.LongCycleExcedances
