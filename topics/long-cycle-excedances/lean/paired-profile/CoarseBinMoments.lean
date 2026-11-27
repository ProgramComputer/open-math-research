import CoarseMomentTables

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances

def coarseShapeIndex (y : ℚ) : Fin 8 :=
  if 1 ≤ y then 7 else if 3/4 ≤ y then 6 else if 1/2 ≤ y then 5 else
  if 1/3 ≤ y then 4 else if 1/6 ≤ y then 3 else if 1/12 ≤ y then 2 else
  if 1/24 ≤ y then 1 else 0

theorem coarse_shape_le {y : ℚ} (hy : 1/48 ≤ y) : coarseMomentFraction (coarseShapeIndex y) ≤ y := by
  unfold coarseShapeIndex
  split_ifs <;> assumption

def coarseBinY (lower upper b : ℕ) : ℚ := max (1/(upper:ℚ)) (1-(b:ℚ)/(4*lower))

private theorem cast_coarseBinY (l u b : ℕ) : (coarseBinY l u b:ℝ)=valueBinFraction l u b := by
  unfold coarseBinY valueBinFraction
  push_cast
  rfl

theorem coarse_bin_moments (lower upper b : ℕ) (hu : 0 < upper) (h48 : upper ≤ 48) :
    zerothMomentBound (valueShape lower upper b) 31 ≤
      (coarseZerothTable (coarseShapeIndex (coarseBinY lower upper b)):ℝ)/linearScale ∧
    firstMomentBound (valueShape lower upper b) 31 ≤
      (coarseFirstTable (coarseShapeIndex (coarseBinY lower upper b)):ℝ)/linearScale := by
  have hy0 : 1/48 ≤ (1:ℚ)/upper := by
    exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hu) (by exact_mod_cast h48)
  have hy : 1/48 ≤ coarseBinY lower upper b := hy0.trans (le_max_left _ _)
  apply coarse_moment_pair
  have hh := div_le_div_of_nonneg_right (coarse_shape_le hy) (by norm_num : (0:ℚ) ≤ 160)
  have hc : ((coarseMomentFraction (coarseShapeIndex (coarseBinY lower upper b))/160:ℚ):ℝ) ≤
      ((coarseBinY lower upper b/160:ℚ):ℝ) := Rat.cast_le.mpr hh
  apply hc.trans_eq
  push_cast
  rw [cast_coarseBinY,valueShape]
  ring

#print axioms coarse_shape_le
#print axioms coarse_bin_moments
end OpenMathResearch.LongCycleExcedances
