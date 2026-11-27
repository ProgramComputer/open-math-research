import CutoffSinglePrimitive
import LinearSlabs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def cutoffSlabLower (j : Fin 9) : ℕ := ![4,6,10,16,22,28,34,40,44] j


def cutoffOuterShape (j : Fin 9) : ℚ := (6/5)/(192*(linearSlabX j:ℚ))

def cutoffInnerShape (j : Fin 9) : ℚ :=
  ((((cutoffSlabLower j)-1:ℕ):ℚ)-1/(linearSlabK j:ℚ))*cutoffOuterShape j

def cutoffMassNat (c : ℚ) : ℕ :=
  (∑ a ∈ signedHead 31, linearWeight c a)+2*linearHalfTail c

def cutoffStarNat (c : ℚ) : ℕ := linearHead c+linearHalfTail c

def cutoffSingleSlabCap (j : Fin 9) : ℚ :=
  ((cutoffMassNat (cutoffOuterShape j):ℚ)/linearScale) *
    ((cutoffStarNat (cutoffInnerShape j):ℚ)/linearScale) /
    (2*(((cutoffSlabLower j)-1).factorial:ℚ)*linearSlabLower j^2)

private theorem cutoff_weight_cast (c : ℚ) (a : ℤ) :
    oddBinKernel (c:ℝ) a ≤ (linearWeight c a:ℝ)/linearScale := by
  apply (le_div_iff₀ (by norm_num [linearScale] : (0:ℝ) < linearScale)).mpr
  let x : ℚ := (linearScale:ℚ)*((1+c*(rationalOdd a^2-1))^(96:ℕ))⁻¹
  have hx : x ≤ (⌈x⌉₊:ℚ) := Nat.le_ceil x
  have h : (x:ℝ) ≤ (linearWeight c a:ℝ) := by
    change (x:ℝ) ≤ (⌈x⌉₊:ℝ)
    exact_mod_cast hx
  dsimp only [x] at h
  push_cast at h
  have hodd : (rationalOdd a:ℝ) = primitiveOddNumber a := by simp [rationalOdd,primitiveOddNumber]
  rw [hodd] at h
  simpa only [oddBinKernel,mul_comm] using h

private theorem cutoff_mass_rounding (c : ℚ) :
    zerothMomentBound (c:ℝ) 31 ≤ (cutoffMassNat c:ℝ)/linearScale := by
  unfold zerothMomentBound cutoffMassNat
  rw [show 2*((31:ℕ):ℝ)+1=63 by norm_num]
  push_cast
  rw [add_div,sum_div]
  exact add_le_add (sum_le_sum (fun a _ => cutoff_weight_cast c a)) (linearTail_upper c)

private theorem cutoff_star_rounding (A : Finset ℤ) (a : ℤ) {c : ℚ}
    (hc : 0 < (c:ℝ)) (hg : 1 ≤ 3*(c:ℝ)*63^2) :
    (∑ q ∈ A.erase a, oddStarTerm (c:ℝ) a q) ≤ (cutoffStarNat c:ℝ)/linearScale := by
  have h := signed_star_envelope A a 31 hc
    (by simpa only [show 2*((31:ℕ):ℝ)+1=63 by norm_num] using hg)
    (linearHead_upper c) (by simpa only [show 2*((31:ℕ):ℝ)+1=63 by norm_num] using linearTail_upper c)
  apply h.trans_eq
  push_cast [cutoffStarNat]
  ring

/-- Nine exact slab bounds for the single primitive at the cutoff atom.
The hierarchy uses the actual cutoff coefficients of the original row. -/
theorem single_cutoff_slab_of_spec (j : Fin 9) {n k : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hlo : cutoffSlabLower j*k ≤ n) (hhi : n ≤ linearSlabX j*k)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) :
    singleCutoffPrimitiveCost k n d θ A ≤
      (cutoffSingleSlabCap j:ℝ) := by
  obtain ⟨hKk,hAlinear⟩ := linearSlabInputs j hn hhi hS hU
  have hK : 193 ≤ linearSlabK j := by fin_cases j <;> norm_num [linearSlabK,linearSlabX]
  have hl : 4 ≤ cutoffSlabLower j := by fin_cases j <;> norm_num [cutoffSlabLower]
  have hX : 0 < (linearSlabX j:ℝ) := by fin_cases j <;> norm_num [linearSlabX]
  have hA₀ : 0 < (linearSlabLower j:ℝ) := by
    fin_cases j <;> norm_num [linearSlabLower, linearSlabQuarter]
  have hAa : (linearSlabLower j:ℝ) ≤ (k:ℝ)*sin θ := hAlinear
  have hOuter : (cutoffOuterShape j:ℝ) = (6/5)/(192*linearSlabX j) := by
    simp [cutoffOuterShape]
  have hInner : (cutoffInnerShape j:ℝ) = ((((cutoffSlabLower j)-1:ℕ):ℝ)-
      1/(linearSlabK j:ℝ))*(6/5)/(192*linearSlabX j) := by
    unfold cutoffInnerShape
    push_cast
    rw [hOuter]
    ring
  have ho0 : 0 < (cutoffOuterShape j:ℝ) := by rw [hOuter]; positivity
  have hoG : 1 ≤ 3*(cutoffOuterShape j:ℝ)*63^2 := by
    fin_cases j <;> norm_num [cutoffOuterShape,linearSlabX]
  have hi0 : 0 < (cutoffInnerShape j:ℝ) := by
    fin_cases j <;> norm_num [cutoffInnerShape,cutoffSlabLower,linearSlabK,linearSlabX,cutoffOuterShape]
  have hiG : 1 ≤ 3*(cutoffInnerShape j:ℝ)*63^2 := by
    fin_cases j <;> norm_num [cutoffInnerShape,cutoffSlabLower,linearSlabK,linearSlabX,cutoffOuterShape]
  have hm := all_pole_zeroth_moment ho0 31
    (by simpa only [show 2*((31:ℕ):ℝ)+1=63 by norm_num] using hoG) A
  have hmR := hm.trans (cutoff_mass_rounding (cutoffOuterShape j))
  have hsR (a : ℤ) := cutoff_star_rounding A a hi0 hiG
  rw [hOuter] at hmR
  simp_rw [hInner] at hsR
  have h := single_cutoff_primitive_lattice
    hd hK hKk hl hlo
    hX (by exact_mod_cast hhi) (by norm_num : (0:ℝ) ≤ 6/5) hS hU hA₀ hAa
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) A hmR hsR
  unfold cutoffSingleSlabCap
  push_cast
  exact h

#print axioms single_cutoff_slab_of_spec
end OpenMathResearch.LongCycleExcedances
