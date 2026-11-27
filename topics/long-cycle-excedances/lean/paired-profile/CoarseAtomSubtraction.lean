import CoarseSlabDominance
import CoarseBinMoments
import RepositoryMultipleAtom
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset
open private slab_degree_mass_nn from CoarseSlabDominance

def coarseSubtract (slab : Fin 9) (b : ℕ) : ℕ :=
  if slab = 0 ∧ 4 ≤ b then
    ⌊(coarseScale:ℚ)*rationalDegreeMass (linearSlabK slab) b*(3/4)/linearSlabLower slab⌋₊
  else 0

set_option maxHeartbeats 1600000 in
theorem coarse_subtract_le (slab : Fin 9) (b : ℕ) :
    2^24*coarseSubtract slab b ≤ linearSlabTable slab b := by
  by_cases h : slab=0 ∧ 4≤b
  · let m := rationalDegreeMass (linearSlabK slab) b
    let A := linearSlabLower slab
    let c := linearShape (linearSlabK slab) b (linearSlabX slab)
    have hm : 0 ≤ m := slab_degree_mass_nn slab h.2
    have hA : 0 < A := by
      dsimp only [A]
      rw [h.1]
      norm_num [linearSlabLower,linearSlabQuarter]
    let x := (coarseScale:ℚ)*m*(3/4)/A
    have hx : 0≤x := by dsimp only [x]; positivity
    have hf : (coarseSubtract slab b:ℚ) ≤ x := by
      rw [coarseSubtract,if_pos h]
      exact Nat.floor_le hx
    have hr := linear_head_lower_two_poles c
    have hg : (2:ℚ)^24*coarseScale*(3/4) ≤ ((linearHead c+linearHalfTail c:ℕ):ℚ) := by
      have scale_eq : (2:ℚ)^24*(coarseScale:ℚ)*(3/4) = ((3*linearScale/4:ℕ):ℚ) := by
        norm_num [coarseScale,linearScale]
      rw [scale_eq]
      exact Nat.cast_le.mpr (hr.trans (Nat.le_add_right _ (linearHalfTail c)))
    have hh : ((2:ℚ)^24)*x ≤ m*((linearHead c+linearHalfTail c:ℕ):ℚ)/A := by
      calc
        _ = m*((2:ℚ)^24*coarseScale*(3/4))/A := by dsimp only [x]; ring
        _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hm) hA.le
    have hn := (mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℚ)≤2^24)).trans hh
    have hc : m*((linearHead c+linearHalfTail c:ℕ):ℚ)/A ≤ (linearSlabTable slab b:ℚ) := by
      unfold linearSlabTable literalLinearTable
      rw [if_neg (by omega : ¬b<4)]
      exact Nat.le_ceil _
    exact_mod_cast hn.trans hc
  · simp [coarseSubtract,h]

def coarseMultipleCost (slab : Fin 9) (lower : ℕ) (q : ℕ → ℕ) : ℚ :=
  let upper := linearSlabX slab
  ∑ b ∈ range 241, if 4*(lower-1)<b ∧ b+5≤5*upper then
    linearSlabLower slab*upper/(6/5)*
      (((q b:ℚ)-(2^24*coarseSubtract slab b:ℕ))/linearScale)*
      ((coarseZerothTable (coarseShapeIndex (coarseBinY lower upper b)):ℚ)/linearScale)
    else 0

theorem coarse_multiple_cost_upper (slab : Fin 9) (lower : ℕ) (q : ℕ→ℕ)
    (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    atomMultipleHeadEstimate slab lower q ≤ (coarseMultipleCost slab lower q:ℝ) := by
  let X := linearSlabX slab
  have hx : X ≤ 48 := by dsimp only [X]; fin_cases slab <;> norm_num [linearSlabX]
  have hu : 0<X := by dsimp only [X]; fin_cases slab <;> norm_num [linearSlabX]
  have hA : (0:ℝ) ≤ linearSlabLower slab := by
    fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  unfold atomMultipleHeadEstimate coarseMultipleCost
  dsimp only
  rw [Rat.cast_sum]
  apply sum_le_sum
  intro b hb
  by_cases h : 4*(lower-1)<b ∧ b+5≤5*linearSlabX slab
  · simp only [if_pos h]
    push_cast
    have hbg := rounded_gap_nonnegative (by decide : 0<linearScale) _ q hq hrec
      (show 0<b by omega) (show b≤240 by have := mem_range.mp hb; omega)
    have hgap : (0:ℝ) ≤ q b-(linearSlabTable slab b:ℝ) := by exact sub_nonneg.mpr (by exact_mod_cast hbg)
    have hsub : (q b:ℝ)-(linearSlabTable slab b:ℝ) ≤
        (q b:ℝ)-(2^24:ℝ)*coarseSubtract slab b := by
      apply sub_le_sub_left
      exact_mod_cast coarse_subtract_le slab b
    rw [show (2:ℝ)^24=16777216 by norm_num] at hsub
    have hm := (coarse_bin_moments lower X b hu hx).1
    have hw : (0:ℝ) ≤ linearSlabLower slab * (linearSlabX slab:ℝ) / (6/5) :=
      div_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hm (mul_nonneg hw (div_nonneg hgap (by positivity)))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsub (by positivity)) hw) (by positivity))
  · simp [h]

#print axioms coarse_subtract_le
#print axioms coarse_multiple_cost_upper
end OpenMathResearch.LongCycleExcedances
