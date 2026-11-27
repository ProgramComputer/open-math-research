import ActualPrincipalPair
import RepositoryPrincipalSlab
import WindowPrincipalLimit

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def principalWindowValue (M j : ℕ) (θ : ℝ) : ℂ :=
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  Complex.exp (∑ q ∈ (symmetricPoleWindow M).erase 0,
    principalLogIntegral j (w/pairedPoleDenom (cos θ) (sin θ) q))

theorem finite_scaled_principal_value (M j : ℕ) {θ : ℝ} (hS : 0 < sin θ) :
    finiteScaledPrincipal M j θ =
      2*(j+2:ℕ)*exp (-cycleHarmonic (j+1))*(principalWindowValue M j θ).re := by
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  let f (q:ℤ) := principalLogIntegral j (w/pairedPoleDenom (cos θ) (sin θ) q)
  have hs : (∑ q ∈ offPrincipalWindow M,f q) = ∑ q ∈ (symmetricPoleWindow M).erase 0, f q := by
    rw [offPrincipalWindow,sum_subtype_eq_sum_filter]
    have he : (symmetricPoleWindow M).filter (· ≠ 0) = (symmetricPoleWindow M).erase 0 := by
      ext q
      simp only [mem_filter,mem_erase,and_comm]
    rw [he]
  have hprod : (∏ q ∈ offPrincipalWindow M, ∑' m,
      PowerSeries.coeff (R := ℂ) m (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 q) * w^m) =
      principalWindowValue M j θ := by
    have he : principalWindowValue M j θ = Complex.exp (∑ q ∈ offPrincipalWindow M,f q) := by
      rw [hs]; rfl
    rw [he,Complex.exp_sum]
    apply prod_congr rfl
    intro q _
    exact (occupied_factor_hasSum_integral j (cos θ) hS.ne' q.property.symm
      (principal_pole_ratio_norm_le _ hS.ne' q)).tsum_eq
  unfold finiteScaledPrincipal
  rw [show j+2-1=j+1 by omega]
  rw [show w=pairedPoleDenom (cos θ) (sin θ) 0 from rfl] at hprod
  rw [hprod]

theorem principal_row_discrepancy (M j n : ℕ) (d : ℕ→ℝ) {θ : ℝ} (hS : 0 < sin θ) :
    finiteScaledPrincipal M j θ -
        2*(j+2:ℕ)*(principalCenteredRow (j+2) n d θ (symmetricPoleWindow M)).re ≤
        doubledPrincipalError j n d (symmetricPoleWindow M) θ := by
  let k : ℝ := (j+2:ℕ)
  let r := principalCenteredRow (j+2) n d θ (symmetricPoleWindow M)
  let v := principalWindowValue M j θ
  let c := exp (-cycleHarmonic (j+1))
  rw [finite_scaled_principal_value M j hS]
  change 2*k*c*v.re-2*k*r.re ≤ 2*‖(k:ℂ)*(r-(c:ℂ)*v)‖
  have h := neg_le_of_abs_le (Complex.abs_re_le_norm ((k:ℂ)*(r-(c:ℂ)*v)))
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re] at h
  linarith only [h]

#print axioms finite_scaled_principal_value
#print axioms principal_row_discrepancy
end OpenMathResearch.LongCycleExcedances
