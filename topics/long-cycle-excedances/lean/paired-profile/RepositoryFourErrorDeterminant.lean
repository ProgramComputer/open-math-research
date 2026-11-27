import OriginalDeterminantLimit
import RepositoryPairedProductLimit

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open Filter Real Finset LongCycleBounds OpenMathResearch.LongCycleExcedances
open scoped Topology

def angularOriginalRow (k m : ℕ) (θ : ℝ) : ℝ :=
  let R := Real.pi/sin θ
  R^m*Band.normalizedEnumerator m k (R*cos θ)/(m.factorial:ℝ)

def scaledOriginalDeterminant (k n : ℕ) (θ : ℝ) : ℝ :=
  (k:ℝ)/sin θ*(sin ((n:ℝ)*θ+θ)*angularOriginalRow k n θ -
    sin ((n:ℝ)*θ)*angularOriginalRow k (n+1) θ)

theorem original_angular_window_limit {k n : ℕ} (hk : 2 ≤ k) {θ : ℝ} (hS : 0 < sin θ)
    (hC : 0 ≤ cos θ) :
    Tendsto (fun M => (k:ℝ)/sin θ*(windowDeterminant k n θ (symmetricPoleWindow M)).re) atTop
      (𝓝 (scaledOriginalDeterminant k n θ)) := by
  let R := Real.pi/sin θ
  let u := R*cos θ
  have hR : 0 < R := div_pos Real.pi_pos hS
  have hu : 0 ≤ u := mul_nonneg hR.le hC
  have hcos : u/R=cos θ := by dsimp only [u]; field_simp [hR.ne']
  have hsin : Real.pi/R=sin θ := by dsimp only [R]; field_simp [Real.pi_ne_zero,hS.ne']
  have h (m:ℕ) : Tendsto (fun A => finiteCoefficient A k (cos θ) (sin θ) m) atTop
      (𝓝 (angularOriginalRow k m θ:ℂ)) := by
    have ht := tendsto_original_scaled_finite_paired_products hk u hu hR m
    rw [hcos,hsin] at ht
    simpa only [finiteCoefficient,angularOriginalRow,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,R,u] using ht
  exact normalized_determinant_limit θ (h n) (h (n+1))

/-- The bounded-aspect determinant of the original enumerators, conditional
only on the rounded integer product data besides the slab and angle hypotheses. -/
theorem original_four_error_determinant (slab : Fin 9) {j n : ℕ}
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n) (hnX : n ≤ linearSlabX slab*(j+2))
    {θ : ℝ} (hS : 0 < sin θ) (hC : 0 ≤ cos θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (q : ℕ→ℕ) (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    originalScaledPrincipal j θ-fourErrorHead slab q ≤ scaledOriginalDeterminant (j+2) n θ := by
  exact limit_slab_determinant slab (CycleProbability.originalProbability_spec (by omega))
    hn hlo hnX hS hU q hq hrec (original_angular_window_limit (by omega) hS hC)

theorem original_determinant_margin (slab : Fin 9) {j n : ℕ}
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n) (hnX : n ≤ linearSlabX slab*(j+2))
    {θ : ℝ} (hS : 0 < sin θ) (hC : 0 ≤ cos θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (q : ℕ→ℕ) (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale)
    {margin : ℝ} (hbudget : fourErrorHead slab q + margin ≤
      if linearSlabX slab ≤ 10 then 54/55 else 6000/12243) :
    margin < scaledOriginalDeterminant (j+2) n θ := by
  have hd := original_four_error_determinant slab hn hlo hnX hS hC hU q hq hrec
  by_cases hsmall : linearSlabX slab ≤ 10
  · rw [if_pos hsmall] at hbudget
    have hp := original_scaled_principal_low hn (hnX.trans (Nat.mul_le_mul_right (j+2) hsmall)) hS hU
    linarith only [hd,hp,hbudget]
  · rw [if_neg hsmall] at hbudget
    have h48 : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
    have hp := original_scaled_principal_all hn (hnX.trans (Nat.mul_le_mul_right (j+2) h48)) hS hU
    linarith only [hd,hp,hbudget]

/-- The four separately rounded component ceilings in each interval, in millionths. -/
def slabTotalErrorUnits (slab : Fin 9) : ℕ := ![537946,408948,87610,71365,84423,106923,137598,161483,164202] slab

theorem slab_margin_budget (slab : Fin 9) :
    (slabTotalErrorUnits slab:ℝ)/10^6 + 325873/10^6 ≤
      if linearSlabX slab ≤ 10 then 54/55 else 6000/12243 := by
  fin_cases slab <;> norm_num [slabTotalErrorUnits,linearSlabX]

theorem original_determinant_of_ledger_cap (slab : Fin 9) {j n : ℕ}
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*(j+2) ≤ n) (hnX : n ≤ linearSlabX slab*(j+2))
    {θ : ℝ} (hS : 0 < sin θ) (hC : 0 ≤ cos θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (q : ℕ→ℕ) (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale)
    (hcap : fourErrorHead slab q ≤ (slabTotalErrorUnits slab:ℝ)/10^6) :
    325873/10^6 < scaledOriginalDeterminant (j+2) n θ := by
  apply original_determinant_margin slab hn hlo hnX hS hC hU q hq hrec
  exact (add_le_add hcap le_rfl).trans (slab_margin_budget slab)

#print axioms slab_margin_budget
#print axioms original_determinant_of_ledger_cap
#print axioms original_angular_window_limit
#print axioms original_four_error_determinant
#print axioms original_determinant_margin
end RepositoryQuotientAudit
