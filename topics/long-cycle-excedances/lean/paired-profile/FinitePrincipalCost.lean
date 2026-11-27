import CenteredPrincipalCost
import PrincipalLatticeProduct

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability Finset

/-- The principal convolution error for the actual finite occupied product.
The only analytic input is a bound on its degree masses. -/
theorem finite_principal_cost {j n : ℕ} {d : ℕ→ℝ} (hd : Spec (j+2) d) (hk : 100 ≤ j+2)
    (C : ℝ) {S : ℝ} (hS : S ≠ 0) (T : Finset ℤ) (hT : 0 ∉ T)
    (idx : ℕ→ℕ) (hi : ∀ t, idx t*(j+2) ≤ n-t) {g : ℕ→ℝ} {E : ℝ} (hsum : HasSum g E)
    (hg : ∀ t, centeredErrorBound (idx t)*
       ‖PowerSeries.coeff (R := ℂ) t (∏ q ∈ T, (1+occupiedPrimitive (j+2) C S 0 q))*
         (pairedPoleDenom C S 0)^t‖ ≤ g t) :
    let Q := ∏ q ∈ T, (1+occupiedPrimitive (j+2) C S 0 q)
    let w := pairedPoleDenom C S 0
    let c : ℂ := (Real.exp (-cycleHarmonic (j+1)):ℂ)
    let P := Complex.exp (∑ q ∈ T, principalLogIntegral j (w/pairedPoleDenom C S q))
    ‖((j+2:ℕ):ℂ)*((∑ t ∈ range (n+1),
       (cutoffWeight (j+2) d (n-t):ℂ)*(PowerSeries.coeff (R := ℂ) t Q*w^t))-c*P)‖ ≤ E := by
  dsimp only
  have hQ := occupied_product_hasSum_integral j C hS 0 T hT
    (fun q _ => principal_pole_ratio_norm_le C hS q)
  have he := centered_principal_cost (m:=j+1) hd hk hQ idx hi hsum hg
  have hscale : (((j+1:ℕ):ℝ)+1:ℂ) = ((j+2:ℕ):ℂ) := by push_cast; ring
  rw [hscale] at he
  exact he

#print axioms finite_principal_cost
end OpenMathResearch.LongCycleExcedances
