import EulerianColorKernel
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset PowerSeries
open scoped Polynomial PowerSeries

/-- Excedance-polynomial transform in the number of labeled colors. -/
def colorTransform (n : ℕ) (P : ℝ[X]) : ℝ⟦X⟧ := (P:ℝ⟦X⟧)*(invOneSubPow ℝ n).val

theorem colorTransform_zero : colorTransform 0 1=1 := by
  simp [colorTransform,invOneSubPow_zero]

theorem colorTransform_mul (a b : ℕ) (P Q : ℝ[X]) :
    colorTransform (a+b) (P*Q) = colorTransform a P * colorTransform b Q := by
  simp [colorTransform,invOneSubPow_add] <;> ring

theorem colorTransform_cycle (A : ℕ → ℝ[X]) (hOne : A 1=1)
    (hrec : ∀ m, A (m+1)=(1+Polynomial.C (m:ℝ)*Polynomial.X)*A m+
      Polynomial.X*(1-Polynomial.X)*(A m).derivative) {a : ℕ} (ha : 2 ≤ a) :
    colorTransform a (Polynomial.X*A (a-1)) = colorPowerSeries (a-1) := by
  have he := color_eulerian_kernel A hOne hrec (m:=a-1) (by omega)
  have hs : a-1+1=a := by omega
  rw [hs] at he
  have hi := (invOneSubPow ℝ a).inv_val
  rw [invOneSubPow_inv_eq_one_sub_pow] at hi
  unfold colorTransform
  push_cast
  rw [←he,mul_comm ((1-X)^a),mul_assoc,hi,mul_one]

/-- Applying the transform to the anchored permutation recurrence yields
the label-anchored color-cycle recurrence. Every coefficient is finite. -/
theorem colorTransform_anchor (A : ℕ → ℝ[X]) (hOne : A 1=1)
    (hrec : ∀ m, A (m+1)=(1+Polynomial.C (m:ℝ)*Polynomial.X)*A m+
      Polynomial.X*(1-Polynomial.X)*(A m).derivative)
    (E : ℕ → ℝ[X]) {n k : ℕ} (hk : 2 ≤ k)
    (hE : E n = ∑ a ∈ Icc k n, Polynomial.C (((n-1).choose (a-1)):ℝ)*
      (Polynomial.X*A (a-1))*E (n-a)) :
    colorTransform n (E n) = ∑ a ∈ Icc k n, C (R := ℝ) (((n-1).choose (a-1)):ℝ)*
      colorPowerSeries (a-1)*colorTransform (n-a) (E (n-a)) := by
  conv_lhs => rw [colorTransform,hE]
  rw [←Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_mul,Polynomial.coe_X,Polynomial.coe_C]
  rw [sum_mul]
  apply sum_congr rfl
  intro a ha
  have he : a+(n-a)=n := Nat.add_sub_of_le (mem_Icc.mp ha).2
  have hfactor := colorTransform_mul a (n-a) (Polynomial.X*A (a-1)) (E (n-a))
  rw [he,colorTransform_cycle A hOne hrec (hk.trans (mem_Icc.mp ha).1)] at hfactor
  unfold colorTransform at hfactor
  push_cast at hfactor
  unfold colorTransform
  linear_combination (C (R := ℝ) (((n-1).choose (a-1)):ℝ))*hfactor

/-- Coefficient of the transform at positive size, including all
distributions of extra bars on the directed edges. -/
theorem colorTransform_coeff (P : ℝ[X]) {n : ℕ} (hn : 0 < n) (p : ℕ) :
    coeff (R := ℝ) p (colorTransform n P) =
      ∑ s ∈ range (p+1), P.coeff s * (((n-1+(p-s)).choose (n-1)):ℝ) := by
  unfold colorTransform
  rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℝ n hn,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk,Polynomial.coeff_coe]

/-- At color count p the power-series product is the finite convolution
over the number of colors in the distinguished cycle. -/
theorem color_convolution_coeff (b : ℝ) (d p : ℕ) (F : ℕ → ℝ) :
    coeff (R := ℝ) p (C (R := ℝ) b*colorPowerSeries d*mk F) =
      b*∑ j ∈ range (p+1), (j:ℝ)^d*F (p-j) := by
  rw [mul_assoc,coeff_C_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [colorPowerSeries,coeff_mk]

#print axioms color_convolution_coeff
#print axioms colorTransform_zero
#print axioms colorTransform_mul
#print axioms colorTransform_cycle
#print axioms colorTransform_anchor
#print axioms colorTransform_coeff
end OpenMathResearch.LongCycleExcedances
