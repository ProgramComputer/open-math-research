import NonprincipalMoment
import NonprincipalValueCost
import LinearSlabs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def valueShape (lower upper b : ℕ) : ℝ := valueBinFraction lower upper b*(6/5)/192

def nonprincipalBinCost (lower upper b : ℕ) :=
  if b+5 ≤ 5*upper then valueBinWeight lower b*firstMomentBound (valueShape lower upper b) 31 else 0

/-- Sum the actual fixed-pole value bound over all nonprincipal poles in a
finite set. Only the 31 positive odd head indices and an explicit first-moment tail remain. -/
theorem nonprincipal_bin_lattice (lower b : ℕ) {upper : ℕ} (hu : 0 < upper) (h48 : upper ≤ 48)
    (T : Finset ℤ) (h0 : 0 ∉ T) (hm : (-1:ℤ) ∉ T) :
    (∑ a ∈ T, valueBinBudget lower upper b a) ≤ nonprincipalBinCost lower upper b := by
  by_cases hb : b+5 ≤ 5*upper
  · simp only [valueBinBudget,nonprincipalBinCost,if_pos hb]
    let c := valueShape lower upper b
    have hur : 0 < (upper:ℝ) := by exact_mod_cast hu
    have h48r : (upper:ℝ) ≤ 48 := by exact_mod_cast h48
    have hfrac : 1/48 ≤ valueBinFraction lower upper b := by
      exact (one_div_le_one_div_of_le hur h48r).trans (le_max_left ..)
    have hc : (1/7680:ℝ) ≤ c := by dsimp [c,valueShape]; linarith
    have hg : 1 ≤ 3*c*(2*((31:ℕ):ℝ)+1)^2 := by norm_num; linarith
    have ht := finite_nonprincipal_first_moment (by linarith : 0 < c) 31 hg T h0 hm
    have hw : 0 ≤ valueBinWeight lower b := by unfold valueBinWeight; split <;> norm_num
    have h := mul_le_mul_of_nonneg_left ht hw
    rw [mul_sum] at h
    apply le_trans _ h
    apply sum_le_sum
    intro a _
    change valueBinWeight lower b*|primitiveOddNumber a| *oWeight c (primitiveOddNumber a) ≤ _
    exact le_of_eq (mul_assoc ..)
  · simp [valueBinBudget,nonprincipalBinCost,hb]

def finiteNonprincipalValueCost (k n : ℕ) (d : ℕ→ℝ) (θ : ℝ) (A : Finset ℤ) : ℝ :=
  ∑ a ∈ (A.erase 0).erase (-1), ∑ t ∈ range (n+2), scaledPoleValueTerm k n t d θ a*
    ‖PowerSeries.coeff (R := ℂ) t (∏ v ∈ A.erase a, (1+occupiedPrimitive k (cos θ) (sin θ) a v))‖

def nonprincipalHeadEstimate (lower upper : ℕ) (q : ℕ→ℕ) : ℝ :=
  ∑ b ∈ range 241, nonprincipalBinCost lower upper b*((q b:ℝ)/linearScale)

theorem nonprincipal_slab_head_of_spec (slab : Fin 9) {k n lower : ℕ} {d : ℕ→ℝ}
    (hd : Spec k d) (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteNonprincipalValueCost k n d θ A ≤ nonprincipalHeadEstimate lower (linearSlabX slab) q := by
  let X := linearSlabX slab
  have h48 : X ≤ 48 := by dsimp [X]; fin_cases slab <;> norm_num [linearSlabX]
  have hpos : 0 < X := by dsimp [X]; fin_cases slab <;> norm_num [linearSlabX]
  have hk : 192 ≤ k := by
    have hmax : n ≤ 48*k := hnX.trans (Nat.mul_le_mul_right k h48)
    omega
  let T := (A.erase 0).erase (-1)
  have h0 : 0 ∉ T := by simp [T]
  have hm : (-1:ℤ) ∉ T := by simp [T]
  have hpoint (a:ℤ) := nonprincipal_value_one_pole hd hk hl h48 hnX hlo hS hU A a
    (by decide : 0 < linearScale) (linearSlabTable slab) q (by simp [linearSlabTable,literalLinearTable])
    hq (fun i _ => literal_slab_linear_envelope_of_spec slab hn hnX hS hU hd A a i) hrec
  apply (sum_le_sum (s:=T) (fun a _ => hpoint a)).trans
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right (nonprincipal_bin_lattice lower b hpos h48 T h0 hm) (by positivity)

theorem original_nonprincipal_value_head (slab : Fin 9) {k n lower : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    finiteNonprincipalValueCost k n (originalProbability k) θ A ≤ nonprincipalHeadEstimate lower (linearSlabX slab) q := by
  have hx : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hmax := hnX.trans (Nat.mul_le_mul_right k hx)
  exact nonprincipal_slab_head_of_spec slab (originalProbability_spec (by omega)) hn hnX hl hlo hS hU A q hq hrec

#print axioms original_nonprincipal_value_head
#print axioms nonprincipal_bin_lattice
#print axioms nonprincipal_slab_head_of_spec
end OpenMathResearch.LongCycleExcedances
