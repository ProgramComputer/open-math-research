import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

private def CM (p q : ℝ[X]) : Prop := ∀ j, p.coeff j ≤ q.coeff j

private theorem cm_add {A B P Q : ℝ[X]} (h : CM A B) (h' : CM P Q) : CM (A+P) (B+Q) :=
  fun j => by simpa only [coeff_add] using add_le_add (h j) (h' j)

private theorem cm_mul {A B P Q : ℝ[X]} (hA : CM 0 A) (hP : CM 0 P) (hAB : CM A B)
    (hPQ : CM P Q) : CM (A*P) (B*Q) := by
  intro j
  simp only [coeff_mul]
  exact sum_le_sum (fun i _ => mul_le_mul (hAB i.1) (hPQ i.2)
    (by simpa using hP i.2) ((by simpa using hA i.1 : 0 ≤ A.coeff i.1).trans (hAB i.1)))

private theorem cm_mul_nn {A B : ℝ[X]} (hA : CM 0 A) (hB : CM 0 B) : CM 0 (A*B) := by
  simpa only [zero_mul] using cm_mul (show CM 0 0 from fun _ => le_rfl)
    (show CM 0 0 from fun _ => le_rfl) hA hB

private theorem cm_add_nn {A B : ℝ[X]} (hA : CM 0 A) (hB : CM 0 B) : CM 0 (A+B) := by
  simpa only [zero_add] using cm_add hA hB

private theorem cm_deriv_nn {A : ℝ[X]} (hA : CM 0 A) : CM 0 (derivative A) := by
  intro j
  rw [coeff_zero,coeff_derivative]
  have ha : 0 ≤ A.coeff (j+1) := by simpa using hA (j+1)
  positivity

/-- The full positive product, its linear part and its strictly multiple-primitive part. -/
def binFull {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) := ∏ i ∈ s, (1+p i)
def binLinear {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) := ∑ i ∈ s, p i
def binMultiple {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) := binFull s p-1-binLinear s p

private theorem bin_insert {ι : Type*} [DecidableEq ι] {i : ι} {s : Finset ι} (hi : i ∉ s)
    (p : ι → ℝ[X]) :
    binMultiple (insert i s) p = binMultiple s p + p i*(binFull s p-1) := by
  simp only [binMultiple,binLinear,binFull,prod_insert hi,sum_insert hi]
  ring

/-- Coefficientwise, the derivative of the multiple-primitive part of a
finite positive product is bounded by L' times its nonconstant part. -/
private theorem bin_product_differential_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ s, ∀ j, 0 ≤ (p i).coeff j) :
    CM 0 (binFull s p-1) ∧ CM 0 (derivative (binLinear s p)) ∧
    CM (derivative (binMultiple s p)) (derivative (binLinear s p)*(binFull s p-1)) := by
  classical
  have oneNN : CM 0 (1:ℝ[X]) := by
    intro j
    rcases j with _|j <;> simp [coeff_one]
  have go : CM 0 (binFull s p-1) ∧ CM 0 (derivative (binLinear s p)) ∧
      CM (derivative (binMultiple s p)) (derivative (binLinear s p)*(binFull s p-1)) := by
    induction s using Finset.induction_on with
    | empty => simp [CM,binMultiple,binFull,binLinear]
    | @insert i s hi ih =>
      obtain ⟨hP,hL,hM⟩ := ih (fun a ha => hp a (mem_insert_of_mem ha))
      have hB : CM 0 (p i) := fun j => by simpa using hp i (mem_insert_self i s) j
      let B := p i
      let P := binFull s p-1
      let E := derivative (binLinear s p)
      have hF : CM 0 (binFull s p) := by
        simpa [P] using cm_add_nn hP oneNN
      have hF' : CM 0 (B*(binFull s p)) := cm_mul_nn hB hF
      have hfull : binFull (insert i s) p-1 = P+B*(binFull s p) := by
        dsimp [binFull,P,B]
        rw [prod_insert hi]
        ring
      have hlin : derivative (binLinear (insert i s) p) = derivative B+E := by
        simp [binLinear,hi,B,E]
      have hder : derivative (binFull s p) = derivative (binMultiple s p)+E := by
        simp only [binMultiple,derivative_sub,derivative_one,sub_zero,E]
        ring
      rw [hfull,hlin]
      refine ⟨cm_add_nn hP hF',cm_add_nn (cm_deriv_nn hB) hL,?_⟩
      rw [bin_insert hi,derivative_add,derivative_mul,derivative_sub,derivative_one,sub_zero]
      have hb := cm_mul (cm_deriv_nn hB) hP (show CM (derivative B) (derivative B) from fun _ => le_rfl)
        (show CM P (P+B*binFull s p) from fun j => by
          simpa only [coeff_add,le_add_iff_nonneg_right,coeff_zero] using hF' j)
      have hd : CM (derivative (binFull s p)) (E * binFull s p) := by
        rw [hder]
        convert cm_add hM (show CM E E from fun _ => le_rfl) using 1
        dsimp [P,E]
        ring
      have hbp : CM (B*derivative (binFull s p)) (B*(E*binFull s p)) :=
        cm_mul hB (by
          rw [show derivative (binFull s p)=derivative (binFull s p-1) by simp]
          exact cm_deriv_nn hP) (fun _ => le_rfl) hd
      have hterm := cm_add (cm_add hM hb) hbp
      convert hterm using 1 <;> dsimp [P,E,B] <;> ring
  exact go

theorem bin_full_nonconstant_nonnegative {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ s, ∀ j, 0 ≤ (p i).coeff j) (j : ℕ) : 0 ≤ (binFull s p-1).coeff j := by
  simpa only [coeff_zero] using (bin_product_differential_bounds s p hp).1 j

theorem bin_multiple_derivative_le {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ s, ∀ j, 0 ≤ (p i).coeff j) (j : ℕ) :
    (derivative (binMultiple s p)).coeff j ≤
      (derivative (binLinear s p)*(binFull s p-1)).coeff j :=
  (bin_product_differential_bounds s p hp).2.2 j

/-- A rounded coefficient recurrence for an exponential majorant controls
both the full product and the mass with two or more primitives. The latter
subtracts the rounded linear envelope, even when it exceeds the actual
one-primitive mass. Only the first N recurrence inequalities are needed. -/
theorem bin_rounded_product_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ[X])
    (hp : ∀ i ∈ s, ∀ j, 0 ≤ (p i).coeff j) (hz : ∀ i ∈ s, (p i).coeff 0=0)
    (L Q : ℝ[X]) (N : ℕ) (hl0 : L.coeff 0=0) (hq0 : Q.coeff 0=1)
    (hL : ∀ j ≤ N, (binLinear s p).coeff j ≤ L.coeff j)
    (hQ : ∀ j < N, (derivative L*Q).coeff j ≤ (derivative Q).coeff j) :
    ∀ n ≤ N, (binFull s p).coeff n ≤ Q.coeff n ∧
      (binMultiple s p).coeff n ≤ (Q-1-L).coeff n := by
  classical
  obtain ⟨hpos,hlin,hder⟩ := bin_product_differential_bounds s p hp
  have hF0 : (binFull s p).coeff 0=1 := by
    unfold binFull
    rw [←constantCoeff_apply, map_prod]
    apply prod_eq_one
    intro i hi
    simp [constantCoeff_apply,hz i hi]
  have hlin0 : (binLinear s p).coeff 0=0 := by
    rw [binLinear,finset_sum_coeff]
    exact sum_eq_zero (fun i hi => hz i hi)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [binMultiple,hF0,hlin0,hl0,hq0]
    | succ m =>
      have hbound : ((derivative (binLinear s p))*(binFull s p-1)).coeff m ≤
          (derivative L*(Q-1)).coeff m := by
        rw [coeff_mul,coeff_mul]
        apply sum_le_sum
        intro ij hij
        have hij' := Finset.mem_antidiagonal.mp hij
        have hstep := (ih ij.2 (by omega) (by omega)).1
        have hright : (binFull s p-1).coeff ij.2 ≤ (Q-1).coeff ij.2 := by
          simpa only [coeff_sub,sub_le_sub_iff_right] using hstep
        have hleft : (derivative (binLinear s p)).coeff ij.1 ≤ (derivative L).coeff ij.1 := by
          rw [coeff_derivative,coeff_derivative]
          exact mul_le_mul_of_nonneg_right (hL (ij.1+1) (by omega)) (by positivity)
        apply mul_le_mul hleft hright
        · simpa only [coeff_zero] using hpos ij.2
        · have hb : (0:ℝ) ≤ (derivative (binLinear s p)).coeff ij.1 := by
            simpa only [coeff_zero] using hlin ij.1
          exact hb.trans hleft
      have hscalar := (hder m).trans hbound
      rw [mul_sub,mul_one,coeff_sub] at hscalar
      have hscaled := hscalar.trans (sub_le_sub_right (hQ m (by omega)) _)
      simp only [coeff_derivative] at hscaled
      have hm : 0 < ((m+1:ℕ):ℝ) := by positivity
      have hmulti : (binMultiple s p).coeff (m+1) ≤ Q.coeff (m+1)-L.coeff (m+1) := by
        apply le_of_mul_le_mul_right _ hm
        simpa only [sub_mul,Nat.cast_add,Nat.cast_one] using hscaled
      have hone : (1:ℝ[X]).coeff (m+1)=0 := by simp [coeff_one]
      have hfull := hmulti
      simp only [binMultiple,coeff_sub,hone,sub_zero] at hfull
      refine ⟨by linarith only [hfull,hL (m+1) hn],?_⟩
      simpa only [coeff_sub,hone,sub_zero] using hmulti

#print axioms bin_multiple_derivative_le
#print axioms bin_rounded_product_bounds
end OpenMathResearch.LongCycleExcedances
