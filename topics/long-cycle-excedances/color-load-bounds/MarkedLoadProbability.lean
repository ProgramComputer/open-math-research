import MarkedColorLoads
import Mathlib.Algebra.BigOperators.Field
import BinomialColorLoad
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset

/-- One marked color orbit of size j has expected multiplicity 1/j; its
load is exactly binomial with n trials and success probability j/p. -/
theorem marked_load_probability {n p i j : ℕ} (hj : 0 < j) (hjp : j ≤ p) (hin : i ≤ n) :
    (Nat.card (MarkedColorLoad n p i j hj):ℝ) / ((p.factorial:ℝ)*(p:ℝ)^n) =
      colorLoad n i ((j:ℝ)/p)/(j:ℝ) := by
  have hpos : (0:ℝ) < p := by exact_mod_cast hj.trans_le hjp
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hf : (j:ℝ)*((j-1).factorial:ℝ)=(j.factorial:ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hj.ne'
  have hc : (p.choose j:ℝ)*(j.factorial:ℝ)*((p-j).factorial:ℝ)=(p.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjp
  have hx : 1-(j:ℝ)/p=((p-j:ℕ):ℝ)/p := by
    rw [Nat.cast_sub hjp,sub_div,div_self hpos.ne']
  rw [marked_color_load_card]
  unfold colorLoad
  rw [hx,div_pow,div_pow]
  push_cast
  apply (div_eq_div_iff (mul_ne_zero (by positivity) (pow_ne_zero _ hpos.ne')) hjpos.ne').2
  have hpow : (p:ℝ)^i*(p:ℝ)^(n-i)=(p:ℝ)^n := by rw [←pow_add,Nat.add_sub_of_le hin]
  rw [←hc,←hf]
  field_simp [hpos.ne']
  linear_combination (p.choose j:ℝ)*(n.choose i:ℝ)*((j-1).factorial:ℝ)*((p-j).factorial:ℝ)*(j:ℝ)^(i+1)*(((p:ℝ)-(j:ℝ))^(n-i))*hpow

private instance markedColorLoadFinite (n p i j : ℕ) (hj : 0 < j) :
    Finite (MarkedColorLoad n p i j hj) := by
  unfold MarkedColorLoad
  infer_instance

/-- Exact first moment over the marked support and load sizes. -/
noncomputable def expectedColorMarks (n p : ℕ) (bad : ℕ → ℕ → Prop) : ℝ := by
  classical
  exact ∑ j : {j : Fin (p+1) // 0 < j.val},
    ∑ i : {i : Fin (n+1) // bad j.val.val i.val},
      colorLoad n i.val.val ((j.val.val:ℝ)/p)/(j.val.val:ℝ)

theorem total_marked_probability (n p : ℕ) (bad : ℕ → ℕ → Prop) :
    (Nat.card (MarkedExceptions n p bad):ℝ)/((p.factorial:ℝ)*(p:ℝ)^n)=
    expectedColorMarks n p bad := by
  classical
  unfold MarkedExceptions expectedColorMarks
  simp only [Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  exact marked_load_probability j.property (by have := j.val.isLt; omega) (by have := i.val.isLt; omega)

/-- Conditional error budget with every term a literal binomial probability.
No independence of the distinct color-orbit loads is assumed. -/
theorem actual_color_probability_comparison (n p k b : ℕ) (hp : 0 < p) :
    let D : ℝ := (p.factorial:ℝ)*(p:ℝ)^n
    let base := (Nat.card (BaselinePairs n p b):ℝ)/D
    let accepted := (Nat.card (Accepted n p k):ℝ)/D
    base-expectedColorMarks n p (fun j i => b ≤ j ∧ i < k) ≤ accepted ∧
    accepted ≤ base+expectedColorMarks n p (fun j i => j < b ∧ k ≤ i) := by
  dsimp only
  have hD : (0:ℝ) < (p.factorial:ℝ)*(p:ℝ)^n := by positivity
  have hh := color_load_cutoff_comparison n p k b
  have hlow : (Nat.card (BaselinePairs n p b):ℝ) ≤ (Nat.card (Accepted n p k):ℝ) +
      (Nat.card (MarkedExceptions n p (fun j i => b ≤ j ∧ i < k)):ℝ) := by exact_mod_cast hh.1
  have hupp : (Nat.card (Accepted n p k):ℝ) ≤ (Nat.card (BaselinePairs n p b):ℝ) +
      (Nat.card (MarkedExceptions n p (fun j i => j < b ∧ k ≤ i)):ℝ) := by exact_mod_cast hh.2
  have lo := div_le_div_of_nonneg_right hlow hD.le
  have hi := div_le_div_of_nonneg_right hupp hD.le
  rw [add_div,total_marked_probability] at lo hi
  exact ⟨by linarith,hi⟩

#print axioms actual_color_probability_comparison
#print axioms total_marked_probability
#print axioms marked_load_probability
end OpenMathResearch.LongCycleExcedances.ColorAnchor
