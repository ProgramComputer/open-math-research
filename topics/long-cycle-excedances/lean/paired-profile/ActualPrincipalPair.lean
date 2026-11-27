import ActualWindowParts
import PrincipalPhase
import PrincipalConjugation

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability
open scoped ComplexConjugate

theorem reflected_value_term {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k)
    (n t M : ℕ) (θ : ℝ) (a : ℤ) :
    conj (poleValueTerm k n t d θ (symmetricPoleWindow M) a) =
      poleValueTerm k n t d θ (symmetricPoleWindow M) (reflectedPole a) := by
  have h := congrArg (PowerSeries.coeff (R := ℂ) t) (conjugate_occupied_product hd hk (cos θ) (sin θ) M a)
  rw [PowerSeries.coeff_map] at h
  unfold poleValueTerm occupiedCoeffAt
  simp only [map_mul,map_sub,map_pow,map_inv₀,Complex.conj_ofReal,conjugate_pole_denom,h]

def principalCenteredRow (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) : ℂ :=
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  ∑ t ∈ range (n+1), (cutoffWeight k d (n-t):ℂ)*(occupiedCoeffAt k t θ A 0*w^t)

theorem principal_value_exact {k : ℕ} (hk : 0 < k) (n : ℕ) (d : ℕ→ℝ) {θ : ℝ}
    (hS : 0 < sin θ) (A : Finset ℤ) :
    (∑ t ∈ range (n+2),poleValueTerm k n t d θ A 0)=(sin θ:ℂ)*principalCenteredRow k n d θ A := by
  unfold principalCenteredRow
  rw [sum_range_succ]
  have hz : poleValueTerm k n (n+1) d θ A 0=0 := by
    simp [poleValueTerm,cutoffWeight,show ¬k ≤ 0 by omega]
  rw [hz,add_zero,mul_sum]
  apply sum_congr rfl
  intro t ht
  have ht' : t ≤ n+1 := by have := mem_range.mp ht; omega
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  let x : ℂ := w*(sin ((n:ℝ)*θ+θ):ℂ)-(sin ((n:ℝ)*θ):ℂ)
  have hφ : w⁻¹^(n+1-t)*x=(sin θ:ℂ)*w^t := principal_phase_cancellation n t ht' θ hS
  let F := occupiedCoeffAt k t θ A 0
  let r : ℂ := cutoffWeight k d (n-t)
  change F*w⁻¹^(n+1-t)*r*x=(sin θ:ℂ)*(r*(F*w^t))
  linear_combination F*r*hφ

theorem principal_pair_exact {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k) (n M : ℕ)
    {θ : ℝ} (hS : 0 < sin θ) :
    ((∑ t ∈ range (n+2), poleValueTerm k n t d θ (symmetricPoleWindow M) 0)+
      (∑ t ∈ range (n+2), poleValueTerm k n t d θ (symmetricPoleWindow M) (-1))).re =
      2*sin θ*(principalCenteredRow k n d θ (symmetricPoleWindow M)).re := by
  have hr : (-1:ℤ)=reflectedPole 0 := by decide
  have hc : (∑ t ∈ range (n+2), poleValueTerm k n t d θ (symmetricPoleWindow M) (-1))=
      conj (∑ t ∈ range (n+2), poleValueTerm k n t d θ (symmetricPoleWindow M) 0) := by
    rw [map_sum]
    apply sum_congr rfl
    intro t _
    rw [hr]
    exact (reflected_value_term hd hk n t M θ 0).symm
  rw [hc,principal_value_exact (by omega : 0 < k) n d hS]
  simp only [Complex.add_re,Complex.conj_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

#print axioms principal_value_exact
#print axioms principal_pair_exact
end OpenMathResearch.LongCycleExcedances
