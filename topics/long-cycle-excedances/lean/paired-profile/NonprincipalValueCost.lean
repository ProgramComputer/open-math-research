import NonprincipalPoleValue
import FiniteWeightedBinCost

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def valueKernel (lower upper b : ℕ) (q : ℤ) :=
  ((1+valueBinFraction lower upper b*(6/5)/192*(primitiveOddNumber q^2-1))^96)⁻¹

def valueBinBudget (lower upper b : ℕ) (q : ℤ) : ℝ :=
  if b+5 ≤ 5*upper then valueBinWeight lower b*|primitiveOddNumber q| *valueKernel lower upper b q else 0

private theorem bin_budget_nonneg (lower upper b : ℕ) (q : ℤ) : 0 ≤ valueBinBudget lower upper b q := by
  unfold valueBinBudget
  split
  · have h : 0 ≤ valueBinWeight lower b := by unfold valueBinWeight; split <;> norm_num
    exact mul_nonneg (mul_nonneg h (abs_nonneg _)) (inv_nonneg.mpr (Even.pow_nonneg (by decide) _))
  · rfl

theorem value_bin_active {k n upper b t : ℕ} (hk : 0 < k) (hX : n ≤ upper*k)
    (ht : k*b ≤ 5*t) (hr : k ≤ n-t) : b+5 ≤ 5*upper := by
  have hn : t+k ≤ n := by omega
  exact Nat.le_of_mul_le_mul_left (show k*(b+5) ≤ k*(5*upper) by nlinarith) hk

/-- Absolute mass of the exact value summand for a fixed angular pole, after
scaling by k/sin(theta). Numerator-difference summands are handled separately. -/
def scaledPoleValueTerm (k n t : ℕ) (d : ℕ→ℝ) (θ : ℝ) (q : ℤ) : ℝ :=
  let w := pairedPoleDenom (cos θ) (sin θ) q
  (k:ℝ)/sin θ*‖w⁻¹^(n+1-t)*(cutoffWeight k d (n-t):ℂ)*
    (w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ))‖

theorem value_term_on_bin {k n lower upper b t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 192 ≤ k) (hl : 0 < lower) (hX : n ≤ upper*k) (hlo : lower*k ≤ n)
    (ht₁ : 4*t ≤ k*b) (ht₂ : k*b ≤ 5*t)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (q : ℤ) :
    scaledPoleValueTerm k n t d θ q ≤ valueBinBudget lower upper b q := by
  by_cases hr : k ≤ n-t
  · have he := value_bin_active (by omega) hX ht₂ hr
    rw [valueBinBudget,if_pos he]
    have hK := value_kernel_on_bin hk hl hX hlo ht₁ hr hS hU q
    have hP := value_probability_on_bin hd (by omega) hlo ht₁ hr
    have hφ := angular_pole_sine_norm ((n:ℝ)*θ) θ hS q
    let w := pairedPoleDenom (cos θ) (sin θ) q
    let u := w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ)
    have hu : ‖u‖/sin θ ≤ |primitiveOddNumber q| := (div_le_iff₀ hS).mpr (by rw [mul_comm |primitiveOddNumber q| (sin θ)]; exact hφ)
    have hval : 0 ≤ valueBinWeight lower b := by unfold valueBinWeight; split <;> norm_num
    have hprod := mul_le_mul (mul_le_mul hP hu (by positivity) hval) hK (by positivity)
      (mul_nonneg hval (abs_nonneg _))
    unfold scaledPoleValueTerm
    dsimp only
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    apply le_trans _ hprod
    dsimp only [u,w]
    exact le_of_eq (by ring)
  · rw [scaledPoleValueTerm,cutoffWeight,if_neg hr]
    simpa using bin_budget_nonneg lower upper b q

/-- The fixed-pole error reduces to at most 236 rounded coefficients for upper
aspect at most 48. The shape of the absolute lattice kernel varies by bin. -/
theorem nonprincipal_value_one_pole {k n lower upper G : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 192 ≤ k) (hl : 0 < lower) (hu : upper ≤ 48) (hX : n ≤ upper*k) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (a : ℤ) (hG : 0 < G) (l q : ℕ→ℕ) (hl0 : l 0=0) (hq : q 0=G)
    (hL : ∀ i ≤ 240, (binLinear (A.erase a) (fun v =>
      forgetDegree (literalMarkedPrimitive k (n+1) (cos θ) (sin θ) a v))).coeff i ≤ (l i:ℝ)/G)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,(ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G) :
    let Q := ∏ v ∈ A.erase a, (1+occupiedPrimitive k (cos θ) (sin θ) a v)
    (∑ t ∈ range (n+2), scaledPoleValueTerm k n t d θ a*‖PowerSeries.coeff (R := ℂ) t Q‖) ≤
      ∑ b ∈ range 241, valueBinBudget lower upper b a*((q b:ℝ)/G) := by
  apply finite_weighted_bin_cost A a (by omega : 0 < k) (cos θ) (sin θ) _ _ _ _ _ _ _ hG l q hl0 hq hL hrec
  · intro v _ t ht
    exact occupied_primitive_below hd (by omega) ht _ _ a v
  · intro t
    unfold scaledPoleValueTerm
    positivity
  · exact fun b => bin_budget_nonneg lower upper b a
  · intro b hb
    simp only [valueBinBudget,if_neg (show ¬b+5 ≤ 5*upper by omega)]
  · intro b t _ ht₁ ht₂
    exact value_term_on_bin hd hk hl hX hlo ht₁ ht₂ hS hU a

#print axioms value_term_on_bin
#print axioms nonprincipal_value_one_pole
end OpenMathResearch.LongCycleExcedances
