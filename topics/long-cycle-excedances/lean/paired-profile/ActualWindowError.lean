import ActualNumeratorCost
import ActualPrincipalPair
import RepositoryNonprincipalCost

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

theorem actual_nonprincipal_mass (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) :
    (∑ a ∈ (A.erase 0).erase (-1), ∑ t ∈ range (n+2), (k:ℝ)/sin θ * ‖poleValueTerm k n t d θ A a‖)=
      finiteNonprincipalValueCost k n d θ A := by
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro t _
  unfold poleValueTerm scaledPoleValueTerm occupiedCoeffAt
  simp only [norm_mul]
  ring

private theorem scalar_double_norm {I J : Type*} (A : Finset I) (B : Finset J) (x : I→J→ℂ)
    {c : ℝ} (hc : 0 ≤ c) :
    c*‖∑ a ∈ A, ∑ t ∈ B,x a t‖ ≤ ∑ a ∈ A, ∑ t ∈ B,c*‖x a t‖ := by
  have h := (norm_sum_le _ _).trans (sum_le_sum (s:=A) (fun a _ => norm_sum_le (B) (x a)))
  simpa only [mul_sum] using mul_le_mul_of_nonneg_left h hc

private theorem split_principal_sum (M : ℕ) (P : ℤ→ℂ) :
    (∑ a ∈ symmetricPoleWindow M, P a)=
      (P 0+P (-1)) + ∑ a ∈ ((symmetricPoleWindow M).erase 0).erase (-1), P a := by
  obtain ⟨h0,hm⟩ := symmetric_pole_window_principals M
  have hme : (-1:ℤ) ∈ (symmetricPoleWindow M).erase 0 := mem_erase.mpr ⟨by decide,hm⟩
  have h := sum_erase_add _ P h0
  rw [←sum_erase_add _ P hme] at h
  rw [←h]
  ring

/-- Signed error bound for the finite determinant against its actual centered
principal row. The three remaining terms are masses of literal coefficients. -/
theorem finite_determinant_against_row {k n : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 2 ≤ k) (hkn : k ≤ n) (M : ℕ) {θ : ℝ} (hS : 0 < sin θ) :
    let A := symmetricPoleWindow M
    2*(k:ℝ)*(principalCenteredRow k n d θ A).re -
      ((k:ℝ)/sin θ)*(windowDeterminant k n θ A).re ≤
        finiteNonprincipalValueCost k n d θ A + finiteRegularCost k n d θ A + finiteCutoffJump k n d θ A := by
  dsimp only
  let A := symmetricPoleWindow M
  let V (t:ℕ) := poleValueTerm k n t d θ A
  let N (t:ℕ) := poleNumeratorTerm k n t d θ A
  let B := range (n+2)
  let P (a:ℤ) := ∑ t ∈ B, V t a
  let T := (A.erase 0).erase (-1)
  let val := ∑ a ∈ T, P a
  let num := ∑ a ∈ A, ∑ t ∈ B, N t a
  let c : ℝ := (k:ℝ)/sin θ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsplit : windowDeterminant k n θ A = (P 0+P (-1))+val-num := by
    rw [finite_determinant_parts hd (by omega) (by omega) hS]
    exact congrArg (·-num) (split_principal_sum M P)
  have he := congrArg Complex.re hsplit
  simp only [Complex.add_re,Complex.sub_re] at he
  have hphase := principal_pair_exact hd hk n M hS
  change (P 0+P (-1)).re = _ at hphase
  simp only [Complex.add_re] at hphase
  have hv : c*(-val.re) ≤ finiteNonprincipalValueCost k n d θ A := by
    apply (mul_le_mul_of_nonneg_left ((neg_le_abs val.re).trans (Complex.abs_re_le_norm val)) hc).trans
    rw [←actual_nonprincipal_mass]
    exact scalar_double_norm T B (fun a t => V t a) hc
  have hnum : c*num.re ≤ finiteRegularCost k n d θ A + finiteCutoffJump k n d θ A := by
    apply (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hc).trans
    rw [←actual_numerator_mass hkn d θ A]
    exact scalar_double_norm A B (fun a t => N t a) hc
  have h := add_le_add hv hnum
  have hscale : c*(2*sin θ*(principalCenteredRow k n d θ A).re)=
      2*(k:ℝ)*(principalCenteredRow k n d θ A).re := by dsimp [c]; field_simp [hS.ne'] <;> ring
  change _ - c*(windowDeterminant k n θ A).re ≤ _
  rw [he,hphase,←hscale]
  linarith only [h]

#print axioms actual_nonprincipal_mass
#print axioms finite_determinant_against_row
end OpenMathResearch.LongCycleExcedances
