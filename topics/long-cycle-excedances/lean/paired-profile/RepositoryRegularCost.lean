import RegularValueCost
import RepositoryNonprincipalCost
import SignedStarEnvelope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def zerothMomentBound (c : ℝ) (J : ℕ) : ℝ :=
  (∑ a ∈ signedHead J, oddBinKernel c a)+oTail c (2*(J:ℝ)+1)/(190*c*(2*(J:ℝ)+1))

theorem all_pole_zeroth_moment {c : ℝ} (hc : 0 < c) (J : ℕ)
    (hg : 1 ≤ 3*c*(2*(J:ℝ)+1)^2) (T : Finset ℤ) :
    (∑ a ∈ T, oddBinKernel c a) ≤ zerothMomentBound c J := by
  rw [←sum_filter_add_sum_filter_not T (fun a => a ∈ signedHead J) (oddBinKernel c)]
  apply add_le_add _ (signed_mass_tail T J hc hg)
  exact sum_le_sum_of_subset_of_nonneg (fun a ha => (mem_filter.mp ha).2)
    (fun a _ _ => inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))

def regularBinCost (lower upper b : ℕ) (A₀ : ℝ) : ℝ :=
  if b+5 ≤ 5*upper then regularBinWeight lower b/A₀*zerothMomentBound (valueShape lower upper b) 31 else 0

theorem regular_bin_lattice (lower b : ℕ) {upper : ℕ} (hu : 0 < upper) (h48 : upper ≤ 48)
    {A₀ : ℝ} (hA : 0 < A₀) (T : Finset ℤ) :
    (∑ a ∈ T, regularPoleBudget lower upper b A₀ a) ≤ regularBinCost lower upper b A₀ := by
  by_cases hb : b+5 ≤ 5*upper
  · simp only [regularPoleBudget,regularBinCost,if_pos hb]
    let c := valueShape lower upper b
    have hur : 0 < (upper:ℝ) := by exact_mod_cast hu
    have h48r : (upper:ℝ) ≤ 48 := by exact_mod_cast h48
    have hfrac : 1/48 ≤ valueBinFraction lower upper b :=
      (one_div_le_one_div_of_le hur h48r).trans (le_max_left ..)
    have hc : (1/7680:ℝ) ≤ c := by dsimp [c,valueShape]; linarith
    have hg : 1 ≤ 3*c*(2*((31:ℕ):ℝ)+1)^2 := by norm_num; linarith
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (all_pole_zeroth_moment (by linarith : 0 < c) 31 hg T)
      (div_nonneg (regularBinWeight_nonneg ..) hA.le)
  · simp [regularPoleBudget,regularBinCost,hb]

def finiteRegularCost (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ range (n+2), scaledRegularTerm k n t d θ a*
    ‖PowerSeries.coeff (R := ℂ) t (∏ v ∈ A.erase a, (1+occupiedPrimitive k (cos θ) (sin θ) a v))‖

def regularHeadEstimate (slab : Fin 9) (lower : ℕ) (q : ℕ→ℕ) : ℝ :=
  ∑ b ∈ range 241, regularBinCost lower (linearSlabX slab) b (linearSlabLower slab)*((q b:ℝ)/linearScale)

theorem regular_slab_head_of_spec (slab : Fin 9) {k n lower : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteRegularCost k n d θ A ≤ regularHeadEstimate slab lower q := by
  have h48 : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hpos : 0 < linearSlabX slab := by fin_cases slab <;> norm_num [linearSlabX]
  have hA : 0 < (linearSlabLower slab:ℝ) := by fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  apply (sum_le_sum (s:=A) (fun a _ => regular_one_pole slab hd hn hnX hl hlo hS hU A a q hq hrec)).trans
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right (regular_bin_lattice lower b hpos h48 hA A) (by positivity)

theorem original_regular_numerator_head (slab : Fin 9) {k n lower : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteRegularCost k n (originalProbability k) θ A ≤ regularHeadEstimate slab lower q := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hmax := hnX.trans (Nat.mul_le_mul_right k hx)
  exact regular_slab_head_of_spec slab (originalProbability_spec (by omega)) hn hnX hl hlo hS hU A q hq hrec

#print axioms original_regular_numerator_head
#print axioms all_pole_zeroth_moment
#print axioms regular_bin_lattice
#print axioms regular_slab_head_of_spec
end OpenMathResearch.LongCycleExcedances
