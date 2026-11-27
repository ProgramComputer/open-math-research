import PrincipalBinHeadTail
import LinearSlabs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def doubledPrincipalError (j n : ℕ) (d : ℕ→ℝ) (A : Finset ℤ) (θ : ℝ) : ℝ :=
  let w := pairedPoleDenom (cos θ) (sin θ) 0
  let Q := ∏ v ∈ A.erase 0, (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 v)
  let value := Complex.exp (∑ v ∈ A.erase 0, principalLogIntegral j (w/pairedPoleDenom (cos θ) (sin θ) v))
  2*‖((j+2:ℕ):ℂ)*((∑ t ∈ range (n+1), (cutoffWeight (j+2) d (n-t):ℂ)*
    (PowerSeries.coeff (R := ℂ) t Q*w^t))-(Real.exp (-cycleHarmonic (j+1)):ℂ)*value)‖

def principalHeadEstimate (lower : ℕ) (q : ℕ→ℕ) : ℝ :=
  2*(∑ b ∈ range 241, centeredErrorBound (centeredBinIndex lower b)*((q b:ℝ)/linearScale))+1/10000

theorem slab_principal_head_tail_of_spec (slab : Fin 9) {j n lower : ℕ} {d : ℕ→ℝ}
    (hd : Spec (j+2) d) (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*(j+2)) (hlo : lower*(j+2) ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    doubledPrincipalError j n d A θ < principalHeadEstimate lower q := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hkn := hnX.trans (Nat.mul_le_mul_right (j+2) hx)
  apply principal_bin_head_tail hd hn hkn hlo hS hU A (by decide : 0 < linearScale)
    (linearSlabTable slab) q (by simp [linearSlabTable,literalLinearTable]) hq _ hrec
  intro N i _
  exact literal_slab_linear_envelope_of_spec slab hn hnX hS hU hd A 0 i

/-- For the original unweighted permutation enumerator only the rounded product
recurrence remains as a numerical hypothesis. -/
theorem original_slab_principal_head_tail (slab : Fin 9) {j n lower : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*(j+2)) (hlo : lower*(j+2) ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    doubledPrincipalError j n (originalProbability (j+2)) A θ < principalHeadEstimate lower q :=
  slab_principal_head_tail_of_spec slab (originalProbability_spec (by omega)) hn hnX hlo hS hU A q hq hrec

#print axioms original_slab_principal_head_tail
#print axioms slab_principal_head_tail_of_spec
end OpenMathResearch.LongCycleExcedances
