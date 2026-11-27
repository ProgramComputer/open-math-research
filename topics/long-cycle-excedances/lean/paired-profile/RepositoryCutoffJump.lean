import RepositoryMultipleAtom
import CutoffSingleSlabs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def finiteCutoffJump (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) : ℝ :=
  ∑ a ∈ A, ((k:ℝ)/sin θ*|numeratorDiff k d k| *
    ‖angularPairedPole a θ‖^k*|sin ((n:ℝ)*θ)|) *
    ‖PowerSeries.coeff (R := ℂ) (n+1-k) (∏ v ∈ A.erase a,
      (1+occupiedPrimitive k (cos θ) (sin θ) a v))‖

theorem cutoff_jump_split {k n : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k) (hn : k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (A : Finset ℤ) :
    finiteCutoffJump k n d θ A ≤ singleCutoffPrimitiveCost k n d θ A + finiteMultipleAtom k (n+1-k) θ A := by
  unfold finiteCutoffJump singleCutoffPrimitiveCost finiteMultipleAtom
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro a _
  let T := n+1-k
  let F := occupiedPrimitive k (cos θ) (sin θ) a
  let H := ∏ v ∈ A.erase a, (1+F v)
  let B := ∑ v ∈ A.erase a, F v
  let M := occupiedMultipleResidual k T θ A a
  have hz : PowerSeries.coeff (R := ℂ) T (1:PowerSeries ℂ) = 0 := by
    have ht : T≠0 := by dsimp [T]; omega
    simp [PowerSeries.coeff_one,ht]
  have he : PowerSeries.coeff (R := ℂ) T H = PowerSeries.coeff (R := ℂ) T B + M := by
    change PowerSeries.coeff (R := ℂ) T H = _+PowerSeries.coeff (R := ℂ) T (H-1-B)
    rw [map_sub,map_sub,hz]
    ring
  have hB : ‖PowerSeries.coeff (R := ℂ) T B‖ ≤ ∑ v ∈ A.erase a, ‖PowerSeries.coeff (R := ℂ) T (F v)‖ := by
    dsimp only [B]
    rw [map_sum]
    exact norm_sum_le _ _
  have hsplit : ‖PowerSeries.coeff (R := ℂ) T H‖ ≤ (∑ v ∈ A.erase a, ‖PowerSeries.coeff (R := ℂ) T (F v)‖)+‖M‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hB le_rfl)
  let ρ := ‖angularPairedPole a θ‖^k
  let w := (k:ℝ)/sin θ*|numeratorDiff k d k| *ρ*|sin ((n:ℝ)*θ)|
  have hw : 0 ≤ w := by dsimp [w,ρ]; positivity
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hwlim : w ≤ ρ/sin θ := by
    have heq : (k:ℝ)/sin θ*|numeratorDiff k d k| *ρ = ρ/sin θ := by
      rw [hd.numeratorDiff_at_cutoff (by omega),abs_of_nonneg (by positivity)]
      field_simp [hS.ne',hkR.ne'] <;> ring
    dsimp only [w]
    rw [heq]
    exact mul_le_of_le_one_right (by dsimp [ρ]; positivity)
      (abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩)
  have h := mul_le_mul_of_nonneg_left hsplit hw
  rw [mul_add] at h
  apply h.trans
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonneg_right hwlim (norm_nonneg _)).trans_eq (by
    change ρ/sin θ*‖M‖=‖M‖*ρ/sin θ
    ring)

theorem cutoff_jump_head_of_spec (slab : Fin 9) {k n : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*k ≤ n) (hnX : n ≤ linearSlabX slab*k)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteCutoffJump k n d θ A ≤
      (cutoffSingleSlabCap slab:ℝ)+atomMultipleHeadEstimate slab (cutoffSlabLower slab) q := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hl : 0 < cutoffSlabLower slab := by fin_cases slab <;> norm_num [cutoffSlabLower]
  have hk : 2 ≤ k := by have := hnX.trans (Nat.mul_le_mul_right k hx); omega
  have hkn : k ≤ n := (show k ≤ cutoffSlabLower slab*k by simpa using Nat.mul_le_mul_right k hl).trans hlo
  apply (cutoff_jump_split hd hk hkn hS A).trans
  exact add_le_add (single_cutoff_slab_of_spec slab hd hn hlo hnX hS hU A)
    (multiple_atom_slab_head slab hd hn hnX hl hlo (by omega) hS hU A q hq hrec)

theorem original_cutoff_jump_head (slab : Fin 9) {k n : ℕ}
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower slab*k ≤ n) (hnX : n ≤ linearSlabX slab*k)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteCutoffJump k n (originalProbability k) θ A ≤
      (cutoffSingleSlabCap slab:ℝ)+atomMultipleHeadEstimate slab (cutoffSlabLower slab) q := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hk : 2 ≤ k := by have := hnX.trans (Nat.mul_le_mul_right k hx); omega
  exact cutoff_jump_head_of_spec slab (originalProbability_spec hk) hn hlo hnX hS hU A q hq hrec

#print axioms cutoff_jump_head_of_spec
#print axioms cutoff_jump_split
#print axioms original_cutoff_jump_head
end OpenMathResearch.LongCycleExcedances
