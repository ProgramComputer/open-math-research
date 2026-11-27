import AtomWindowAggregate

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def atomMultipleHeadEstimate (slab : Fin 9) (lower : ℕ) (q : ℕ→ℕ) :=
  let upper := linearSlabX slab
  let A₀ : ℝ := linearSlabLower slab
  ∑ b ∈ range 241, if 4*(lower-1) < b ∧ b+5 ≤ 5*upper then
    A₀*upper/(6/5)*(((q b:ℝ)-(linearSlabTable slab b:ℝ))/linearScale)*
      zerothMomentBound (valueShape lower upper b) 31 else 0

/-- The complete scaled cutoff error arising from at least two occupied
primitives. The exact residual is taken before bounding its coefficient. -/
def finiteMultipleAtom (k t : ℕ) (θ : ℝ) (A : Finset ℤ) : ℝ :=
  ∑ a ∈ A, ‖occupiedMultipleResidual k t θ A a‖*
    ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k/sin θ

theorem multiple_atom_slab_head (slab : Fin 9) {k n lower t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    (he : t+k=n+1) {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (q : ℕ→ℕ) (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteMultipleAtom k t θ A ≤ atomMultipleHeadEstimate slab lower q := by
  let upper := linearSlabX slab
  have hx : upper ≤ 48 := by dsimp [upper]; fin_cases slab <;> norm_num [linearSlabX]
  have hu : 0 < upper := by dsimp [upper]; fin_cases slab <;> norm_num [linearSlabX]
  have hA : 0 < (linearSlabLower slab:ℝ) := by fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  apply (sum_le_sum (s:=A) (fun a _ => atom_multiple_one_pole slab hd hn hnX hl hlo he hS hU A a q hq hrec)).trans
  rw [sum_comm]
  unfold atomMultipleHeadEstimate
  dsimp only
  apply sum_le_sum
  intro b hb
  by_cases h : 4*(lower-1) < b ∧ b+5 ≤ 5*upper
  · dsimp only [upper] at h
    simp only [atomMultiplePoleBudget,if_pos h]
    rw [←mul_sum]
    let c := valueShape lower upper b
    have hfrac : 1/48 ≤ valueBinFraction lower upper b :=
      (one_div_le_one_div_of_le (by exact_mod_cast hu : (0:ℝ) < upper) (by exact_mod_cast hx : (upper:ℝ) ≤ 48)).trans
        (le_max_left ..)
    have hc : (1/7680:ℝ) ≤ c := by dsimp [c,valueShape]; linarith
    have hg : 1 ≤ 3*c*(2*((31:ℕ):ℝ)+1)^2 := by norm_num; linarith
    have hg₀ := rounded_gap_nonnegative (by decide : 0 < linearScale) _ q hq hrec
      (show 0 < b by omega) (show b ≤ 240 by have := mem_range.mp hb; omega)
    have hgap : 0 ≤ (q b:ℝ)-(linearSlabTable slab b:ℝ) := sub_nonneg.mpr (by exact_mod_cast hg₀)
    exact mul_le_mul_of_nonneg_left (all_pole_zeroth_moment (by linarith : 0 < c) 31 hg A)
      (mul_nonneg (by positivity) (div_nonneg hgap (by positivity)))
  · dsimp only [upper] at h
    simp [atomMultiplePoleBudget,h]

#print axioms multiple_atom_slab_head
end OpenMathResearch.LongCycleExcedances
