import LiteralBinSupport
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

/-- The majorant holds after forgetting the bin marker; the inner exponent
still records the original total degree. -/
private def Dominates (N : ℕ) (F : PowerSeries ℂ) (P : ℝ[X]) : Prop :=
  ∀ d ≤ N, ‖PowerSeries.coeff (R := ℂ) d F‖ ≤ P.coeff d

private theorem dominates_one (N : ℕ) : Dominates N 1 1 := by
  intro d _
  by_cases h : d=0 <;> simp [PowerSeries.coeff_one,coeff_one,h]

private theorem dominates_one_add {N : ℕ} {F : PowerSeries ℂ} {P : ℝ[X]} (h : Dominates N F P) :
    Dominates N (1+F) (1+P) := by
  intro d hd
  rw [map_add,coeff_add]
  exact (norm_add_le _ _).trans (add_le_add (dominates_one N d hd) (h d hd))

private theorem dominates_mul {N : ℕ} {F G : PowerSeries ℂ} {P Q : ℝ[X]}
    (hf : Dominates N F P) (hg : Dominates N G Q) : Dominates N (F*G) (P*Q) := by
  intro d hd
  rw [PowerSeries.coeff_mul,coeff_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hx := mem_antidiagonal.mp hp
  have hh := hf p.1 (by omega)
  have hh' := hg p.2 (by omega)
  rw [norm_mul]
  exact mul_le_mul hh hh' (norm_nonneg _) ((norm_nonneg _).trans hh)

private theorem dominates_prod {ι : Type*} (A : Finset ι) (N : ℕ)
    (F : ι → PowerSeries ℂ) (P : ι → ℝ[X]) (h : ∀ i ∈ A, Dominates N (F i) (P i)) :
    Dominates N (∏ i ∈ A, F i) (∏ i ∈ A, P i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using dominates_one N
  | @insert i A hi ih =>
    rw [prod_insert hi,prod_insert hi]
    exact dominates_mul (h i (mem_insert_self ..)) (ih fun q hq => h q (mem_insert_of_mem hq))

private theorem eval_mark_degree (k N : ℕ) (c : ℕ→ℝ) (d : ℕ) :
    ((markDegreeBin k N c).eval 1).coeff d = if d ∈ Icc k N then c d else 0 := by
  simp only [markDegreeBin,eval_finsetSum,eval_monomial,one_pow,mul_one,finsetSum_coeff]
  by_cases hd : d ∈ Icc k N
  · rw [if_pos hd,sum_eq_single_of_mem d hd]
    · simp
    · intro s _ hs
      simp [coeff_monomial,hs]
  · rw [if_neg hd]
    apply sum_eq_zero
    intro s hs
    have hne : s ≠ d := by rintro rfl; exact hd hs
    simp [coeff_monomial,hne]

/-- The norm of an actual product coefficient is bounded by the sum of all
nonnegative bin contributions at that degree. A single degree can span many bins. -/
theorem marked_product_dominates {ι : Type*} (A : Finset ι) (k N : ℕ)
    (F : ι → PowerSeries ℂ) (hF : ∀ i ∈ A, ∀ d < k, PowerSeries.coeff (R := ℂ) d (F i)=0)
    {t : ℕ} (ht : t ≤ N) :
    let P := fun q => markDegreeBin k N (fun d => ‖PowerSeries.coeff (R := ℂ) d (F q)‖)
    ‖PowerSeries.coeff (R := ℂ) t (∏ q ∈ A, (1+F q))‖ ≤
      ((∏ q ∈ A, (1+P q)).eval 1).coeff t := by
  dsimp only
  rw [eval_prod]
  apply dominates_prod A N _ _ _ t ht
  intro q hq
  rw [eval_add,eval_one]
  apply dominates_one_add
  intro d hd
  rw [eval_mark_degree]
  by_cases h : k ≤ d
  · simp [mem_Icc,h,hd]
  · simp [mem_Icc,h,hF q hq d (lt_of_not_ge h)]

#print axioms marked_product_dominates
end OpenMathResearch.LongCycleExcedances
