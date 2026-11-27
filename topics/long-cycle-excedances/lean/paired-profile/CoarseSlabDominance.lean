import CoarseLinearComparison
import CoarseRecurrence

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

private theorem slab_degree_mass_nn (slab : Fin 9) {i : ℕ} (hi : 4 ≤ i) :
    0 ≤ rationalDegreeMass (linearSlabK slab) i := by
  by_cases ht : i≤8
  · interval_cases i <;> fin_cases slab <;> norm_num [rationalDegreeMass,rationalDegreeFloor,linearSlabX,linearSlabK]
  · simp only [rationalDegreeMass,if_neg (show ¬i<4 by omega),if_neg (show i≠4 by omega),if_neg ht]
    positivity

private theorem slab_shape_min (slab : Fin 9) {i : ℕ} (hi : 4 ≤ i) :
    0<coarseStarShape slab ∧ coarseStarShape slab ≤ linearShape (linearSlabK slab) i (linearSlabX slab) := by
  have hfloor : 1 ≤ rationalDegreeFloor i := by
    by_cases hs : i=4
    · simp [rationalDegreeFloor,hs]
    · simp [rationalDegreeFloor,hs]
      have hh : (4:ℚ) ≤ ((i-1:ℕ):ℚ) := by exact_mod_cast (show 4 ≤ i-1 by omega)
      linarith
  constructor
  · fin_cases slab <;> norm_num [coarseStarShape,linearShape,linearSlabK,linearSlabX,rationalDegreeFloor]
  · unfold coarseStarShape linearShape
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    simpa only [sub_le_sub_iff_right] using (by simpa [rationalDegreeFloor] using hfloor : rationalDegreeFloor 4 ≤ rationalDegreeFloor i)

/-- One exact lattice upper bound per slab controls all 241 actual linear
table entries. The outward 32-bit coefficients lift to the historical 56-bit scale. -/
theorem coarse_slab_dominates (slab : Fin 9) (i : ℕ)
    (hcap : linearHead (coarseStarShape slab)+linearHalfTail (coarseStarShape slab) ≤
      coarseStarNumerator slab*(linearScale/256)) :
    linearSlabTable slab i ≤ 2^24 * coarseLinear slab i := by
  by_cases ht : i<4
  · simp [linearSlabTable,coarseLinear,literalLinearTable,ht]
  let K := linearSlabK slab
  let X₀ := linearSlabX slab
  let M := rationalDegreeMass K i
  let A := linearSlabLower slab
  let d := linearShape K i X₀
  have hi : 4 ≤ i := by omega
  obtain ⟨hc,hcd⟩ := slab_shape_min slab hi
  have hh := (Nat.add_le_add (linear_head_antitone hc.le hcd) (linear_half_tail_antitone hc hcd)).trans hcap
  have hm : 0 ≤ M := slab_degree_mass_nn slab hi
  have hA : 0<A := by dsimp [A]; fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  have hhead : ((linearHead d+linearHalfTail d:ℕ):ℚ) ≤
      (coarseStarNumerator slab:ℚ)*((2:ℚ)^56/256) := by
    have hdv : ((linearScale/256:ℕ):ℚ)=(2:ℚ)^56/256 := by norm_num [linearScale]
    rw [←hdv]
    exact_mod_cast hh
  have hle : M*((linearHead d+linearHalfTail d:ℕ):ℚ)/A ≤
      (2:ℚ)^24*((coarseScale:ℚ)*M*((coarseStarNumerator slab:ℚ)/256)/A) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhead hm) hA.le).trans_eq
    norm_num [coarseScale]
    ring
  change literalLinearTable K X₀ A i ≤ _
  rw [literalLinearTable,if_neg ht,Nat.ceil_le]
  change M*((linearHead d+linearHalfTail d:ℕ):ℚ)/A ≤ _
  apply hle.trans
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,coarseLinear,if_neg ht]
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)

#print axioms coarse_slab_dominates
end OpenMathResearch.LongCycleExcedances
