import LiteralBinSupport

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

private def EqThrough (N : ℕ) (P Q : ℝ[X][X]) : Prop :=
  ∀ b d, d ≤ N → (P.coeff b).coeff d = (Q.coeff b).coeff d

private theorem eqThrough_mul {N : ℕ} {P P' Q Q' : ℝ[X][X]}
    (hP : EqThrough N P P') (hQ : EqThrough N Q Q') : EqThrough N (P*Q) (P'*Q') := by
  intro b d hd
  simp only [coeff_mul,finsetSum_coeff]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j hj
  have h := mem_antidiagonal.mp hj
  rw [hP _ _ (by omega),hQ _ _ (by omega)]

private theorem eqThrough_prod {ι : Type*} (A : Finset ι) {N : ℕ}
    (P Q : ι → ℝ[X][X]) (h : ∀ i ∈ A, EqThrough N (P i) (Q i)) :
    EqThrough N (∏ q ∈ A, P q) (∏ q ∈ A, Q q) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [EqThrough]
  | @insert i A hi ih =>
    rw [prod_insert hi,prod_insert hi]
    exact eqThrough_mul (h i (mem_insert_self ..)) (ih (fun q hq => h q (mem_insert_of_mem hq)))

/-- Increasing the primitive degree truncation above the extracted degree
does not change the chosen bivariate multiple-primitive coefficient. -/
theorem literal_multiple_truncation (A : Finset ℤ) (k N N' : ℕ) (hNN : N ≤ N')
    (C S : ℝ) (a : ℤ) (b d : ℕ) (hd : d ≤ N) :
    ((markedMultiple (A.erase a) (literalMarkedPrimitive k N C S a)).coeff b).coeff d =
    ((markedMultiple (A.erase a) (literalMarkedPrimitive k N' C S a)).coeff b).coeff d := by
  unfold markedMultiple
  simp only [finsetSum_coeff]
  apply sum_congr rfl
  intro s _
  apply eqThrough_prod s _ _ (N:=N) _ b d hd
  intro q _ bin deg hdeg
  simp only [literalMarkedPrimitive,coeff_markDegreeBin,mem_Icc,hdeg,
    hdeg.trans hNN,and_true]

#print axioms literal_multiple_truncation
end OpenMathResearch.LongCycleExcedances
