import ActualWindowError
import FiniteCarrierError

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Filter CycleProbability
open scoped Topology

def fourErrorHead (slab : Fin 9) (q : ℕ→ℕ) : ℝ :=
  let lower := cutoffSlabLower slab
  principalHeadEstimate lower q + nonprincipalHeadEstimate lower (linearSlabX slab) q +
    regularHeadEstimate slab lower q + ((cutoffSingleSlabCap slab:ℝ)+atomMultipleHeadEstimate slab lower q)

/-- All four errors for the literal finite determinant. Both conjugate
principal terms are included exactly and each numerical head is used once. -/
theorem finite_slab_determinant (slab : Fin 9) {j n : ℕ} {d : ℕ→ℝ} (hd : Spec (j+2) d)
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n) (hnX : n ≤ linearSlabX slab*(j+2))
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (M : ℕ)
    (q : ℕ→ℕ) (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteScaledPrincipal M j θ - ((j+2:ℕ):ℝ)/sin θ*
      (windowDeterminant (j+2) n θ (symmetricPoleWindow M)).re < fourErrorHead slab q := by
  let A := symmetricPoleWindow M
  let lower := cutoffSlabLower slab
  have hl : 0 < lower := by dsimp [lower]; fin_cases slab <;> norm_num [cutoffSlabLower]
  have hkn : j+2 ≤ n := (show j+2 ≤ lower*(j+2) by simpa using Nat.mul_le_mul_right (j+2) hl).trans hlo
  have he := finite_determinant_against_row hd (by omega) hkn M hS
  have hp := principal_row_discrepancy M j n d hS
  have h₁ := slab_principal_head_tail_of_spec slab hd hn hnX hlo hS hU A q hq hrec
  have h₂ := nonprincipal_slab_head_of_spec slab hd hn hnX hl hlo hS hU A q hq hrec
  have h₃ := regular_slab_head_of_spec slab hd hn hnX hl hlo hS hU A q hq hrec
  have h₄ := cutoff_jump_head_of_spec slab hd hn hlo hnX hS hU A q hq hrec
  dsimp only [A,lower] at h₁ h₂ h₃ h₄
  unfold fourErrorHead
  dsimp only at he ⊢
  linarith only [he,hp,h₁,h₂,h₃,h₄]

/-- The finite pole-set errors control the actual limiting determinant
without any termwise interchange involving the rounded bins. -/
theorem limit_slab_determinant (slab : Fin 9) {j n : ℕ} {d : ℕ→ℝ} (hd : Spec (j+2) d)
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n) (hnX : n ≤ linearSlabX slab*(j+2))
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (q : ℕ→ℕ) (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale)
    {value : ℝ} (hD : Tendsto (fun M => ((j+2:ℕ):ℝ)/sin θ*
      (windowDeterminant (j+2) n θ (symmetricPoleWindow M)).re) atTop (𝓝 value)) :
    originalScaledPrincipal j θ - fourErrorHead slab q ≤ value := by
  apply determinant_of_window_errors hS hD
  exact Eventually.of_forall (fun M => (finite_slab_determinant slab hd hn hlo hnX hS hU M q hq hrec).le)

#print axioms finite_slab_determinant
#print axioms limit_slab_determinant
end OpenMathResearch.LongCycleExcedances
