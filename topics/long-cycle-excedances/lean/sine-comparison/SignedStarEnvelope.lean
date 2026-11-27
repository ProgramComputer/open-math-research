import DiscreteOddTail
import PrimitiveLinearEnvelope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def signedHead (J : ℕ) := Icc (-((J:ℤ)+1)) (J:ℤ)
def signedCenters (J : ℕ) := Icc (-((J:ℤ)+2)) ((J:ℤ)+1)

private def upperTailIndex (J : ℕ) (q : ℤ) : ℕ := (q-((J:ℤ)+1)).toNat
private def lowerTailIndex (J : ℕ) (q : ℤ) : ℕ := (-q-((J:ℤ)+2)).toNat

private theorem signed_odd_upper_offset {J : ℕ} {q : ℤ} (h : (J:ℤ) < q) :
    primitiveOddNumber q = (2*(J:ℝ)+1)+2*((upperTailIndex J q:ℝ)+1) := by
  have h' : 0 ≤ q-((J:ℤ)+1) := by omega
  have he := Int.toNat_of_nonneg h'
  have hcast : ((upperTailIndex J q:ℕ):ℝ) = (q:ℝ)-((J:ℝ)+1) := by
    exact_mod_cast he
  unfold primitiveOddNumber
  linarith

private theorem signed_odd_lower_offset {J : ℕ} {q : ℤ} (h : q < -((J:ℤ)+1)) :
    -(primitiveOddNumber q) = (2*(J:ℝ)+1)+2*((lowerTailIndex J q:ℝ)+1) := by
  have h' : 0 ≤ -q-((J:ℤ)+2) := by omega
  have he := Int.toNat_of_nonneg h'
  have hcast : ((lowerTailIndex J q:ℕ):ℝ) = -(q:ℝ)-((J:ℝ)+2) := by
    exact_mod_cast he
  unfold primitiveOddNumber
  linarith

private theorem oWeight_neg (c p : ℝ) : oWeight c (-p) = oWeight c p := by simp [oWeight,oBase,neg_sq]

/-- Signed finite mass tail with the exact scalar from the checkers. -/
theorem signed_mass_tail (A : Finset ℤ) (J : ℕ) {c : ℝ} (hc : 0<c)
    (hg : 1 ≤ 3*c*(2*(J:ℝ)+1)^2) :
    (∑ q ∈ A.filter (fun q => q ∉ signedHead J), oddBinKernel c q) ≤
      oTail c (2*(J:ℝ)+1)/(190*c*(2*(J:ℝ)+1)) := by
  let P := 2*(J:ℝ)+1
  let L := A.filter (fun q => q < -((J:ℤ)+1))
  let H := A.filter (fun q => (J:ℤ)<q)
  let f := fun j : ℕ => (P+2*((j:ℝ)+1))*oWeight c (P+2*((j:ℝ)+1))
  have hP : 1 ≤ P := by dsimp [P]; linarith [Nat.cast_nonneg (α:=ℝ) J]
  have hp : 0 < P := by linarith
  have hf (j : ℕ) : 0 ≤ f j := by
    dsimp [f,oWeight]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
  have hs : Summable f := summable_of_sum_range_le hf (odd_tail_finite_prefix hc hP hg)
  have ht : (∑' j, f j) ≤ oTail c P/(380*c) :=
    Real.tsum_le_of_sum_range_le hf (odd_tail_finite_prefix hc hP hg)
  have hcut : A.filter (fun q => q ∉ signedHead J) = L∪H := by
    ext q
    simp only [L,H,signedHead,mem_filter,mem_union,mem_Icc]
    by_cases hq : q ∈ A <;> simp [hq] <;> omega
  have hdis : Disjoint L H := by
    apply disjoint_left.mpr
    intro q hq hr
    have hq' := (mem_filter.mp hq).2
    have hr' := (mem_filter.mp hr).2
    omega
  have hlo : (∑ q ∈ L, oddBinKernel c q) ≤ oTail c P/(380*c)/P := by
    have hmap : (∑ j ∈ L.image (lowerTailIndex J), f j) =
        ∑ q ∈ L, f (lowerTailIndex J q) := by
      apply sum_image
      intro q hq r hr he
      have eq := Int.toNat_of_nonneg (show 0 ≤ -q-((J:ℤ)+2) by
        have := (mem_filter.mp hq).2
        omega)
      have er := Int.toNat_of_nonneg (show 0 ≤ -r-((J:ℤ)+2) by
        have := (mem_filter.mp hr).2
        omega)
      dsimp [lowerTailIndex] at he
      omega
    have hb : (∑ q ∈ L, f (lowerTailIndex J q)) ≤ oTail c P/(380*c) :=
      hmap ▸ ((hs.sum_le_tsum _ (fun j _ => hf j)).trans ht)
    apply le_trans _ (div_le_div_of_nonneg_right hb hp.le)
    rw [div_eq_mul_inv,sum_mul]
    apply sum_le_sum
    intro q hq
    have hoff := signed_odd_lower_offset (mem_filter.mp hq).2
    have he : oddBinKernel c q = oWeight c (P+2*((lowerTailIndex J q:ℝ)+1)) := by
      change oWeight c (primitiveOddNumber q) = _
      rw [← hoff,oWeight_neg]
    dsimp only [f]
    rw [he,mul_comm _ (oWeight _ _),mul_assoc]
    apply le_mul_of_one_le_right (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
    rw [← div_eq_mul_inv]
    exact (one_le_div hp).mpr (le_add_of_nonneg_right (by positivity))
  have hhi : (∑ q ∈ H, oddBinKernel c q) ≤ oTail c P/(380*c)/P := by
    have hmap : (∑ j ∈ H.image (upperTailIndex J), f j) =
        ∑ q ∈ H, f (upperTailIndex J q) := by
      apply sum_image
      intro q hq r hr he
      have eq := Int.toNat_of_nonneg (show 0 ≤ q-((J:ℤ)+1) by
        have := (mem_filter.mp hq).2
        omega)
      have er := Int.toNat_of_nonneg (show 0 ≤ r-((J:ℤ)+1) by
        have := (mem_filter.mp hr).2
        omega)
      dsimp [upperTailIndex] at he
      omega
    have hb : (∑ q ∈ H, f (upperTailIndex J q)) ≤ oTail c P/(380*c) :=
      hmap ▸ ((hs.sum_le_tsum _ (fun j _ => hf j)).trans ht)
    apply le_trans _ (div_le_div_of_nonneg_right hb hp.le)
    rw [div_eq_mul_inv,sum_mul]
    apply sum_le_sum
    intro q hq
    have hoff := signed_odd_upper_offset (mem_filter.mp hq).2
    have he : oddBinKernel c q = oWeight c (P+2*((upperTailIndex J q:ℝ)+1)) := by
      change oWeight c (primitiveOddNumber q) = _
      rw [hoff]
    dsimp only [f]
    rw [he,mul_comm _ (oWeight _ _),mul_assoc]
    apply le_mul_of_one_le_right (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
    rw [← div_eq_mul_inv]
    exact (one_le_div hp).mpr (le_add_of_nonneg_right (by positivity))
  rw [hcut,sum_union hdis]
  apply (add_le_add hlo hhi).trans_eq
  change _ = oTail c P/(190*c*P)
  ring

def oddStarTerm (c : ℝ) (a q : ℤ) : ℝ :=
  oddBinKernel c q / |primitiveOddNumber q-primitiveOddNumber a|

private theorem oddStarTerm_nonneg (c : ℝ) (a q : ℤ) : 0 ≤ oddStarTerm c a q :=
  div_nonneg (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _)) (abs_nonneg _)

private theorem odd_gap_ge_two {q a : ℤ} (h : q ≠ a) :
    2 ≤ |primitiveOddNumber q-primitiveOddNumber a| := by
  have hgap : (1:ℝ) ≤ |((q-a:ℤ):ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (show (1:ℤ) ≤ |q-a| from Int.add_one_le_iff.mpr (abs_pos.mpr (sub_ne_zero.mpr h)))
  have he : primitiveOddNumber q-primitiveOddNumber a = 2*((q-a:ℤ):ℝ) := by
    simp only [primitiveOddNumber,Int.cast_sub]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

private def clampStarCenter (J : ℕ) (a : ℤ) : ℤ :=
  max (-((J:ℤ)+2)) (min ((J:ℤ)+1) a)

private theorem clamp_mem_signedCenters (J : ℕ) (a : ℤ) :
    clampStarCenter J a ∈ signedCenters J := by
  simp only [clampStarCenter,signedCenters,mem_Icc]
  have hJ : (0:ℤ) ≤ J := Int.natCast_nonneg _
  omega

private theorem odd_gap_clamp {J : ℕ} {a q : ℤ} (hq : q ∈ signedHead J) :
    |primitiveOddNumber q-primitiveOddNumber (clampStarCenter J a)| ≤
      |primitiveOddNumber q-primitiveOddNumber a| := by
  have hJ : (0:ℤ) ≤ J := Int.natCast_nonneg _
  obtain ⟨hl,hh⟩ := mem_Icc.mp hq
  by_cases ha : a < -((J:ℤ)+2)
  · have he : clampStarCenter J a = -((J:ℤ)+2) := by unfold clampStarCenter; omega
    rw [he]
    have hqR : (((-((J:ℤ)+1)):ℤ):ℝ) ≤ (q:ℝ) := Int.cast_le.mpr hl
    have haR : (a:ℝ) < (((-((J:ℤ)+2)):ℤ):ℝ) := Int.cast_lt.mpr ha
    push_cast at hqR haR
    unfold primitiveOddNumber
    push_cast
    rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
    linarith
  by_cases ha' : (J:ℤ)+1 < a
  · have he : clampStarCenter J a = (J:ℤ)+1 := by unfold clampStarCenter; omega
    rw [he]
    have hqR : (q:ℝ) ≤ J := by exact_mod_cast hh
    have haR : (J:ℝ)+1 < a := by exact_mod_cast ha'
    unfold primitiveOddNumber
    push_cast
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · have he : clampStarCenter J a = a := by unfold clampStarCenter; omega
    rw [he]

/-- The checker needs only centers in the head interval and its two
nearest external centers. Tail denominators are at least two. -/
theorem signed_star_envelope (A : Finset ℤ) (a : ℤ) (J : ℕ) {c V T : ℝ}
    (hc : 0<c) (hg : 1 ≤ 3*c*(2*(J:ℝ)+1)^2)
    (hhead : ∀ t ∈ signedCenters J, (∑ q ∈ (signedHead J).erase t, oddStarTerm c t q) ≤ V)
    (htail : oTail c (2*(J:ℝ)+1)/(190*c*(2*(J:ℝ)+1)) ≤ T) :
    (∑ q ∈ A.erase a, oddStarTerm c a q) ≤ V+T/2 := by
  let b := clampStarCenter J a
  let F := A.erase a
  have hsub : F.filter (fun q => q ∈ signedHead J) ⊆ (signedHead J).erase b := by
    intro q hq
    obtain ⟨hqa,hqh⟩ := mem_filter.mp hq
    have he : q ≠ b := by
      intro h
      have hh := mem_Icc.mp hqh
      have h' := (mem_erase.mp hqa).1
      dsimp [b,clampStarCenter] at h
      omega
    exact mem_erase.mpr ⟨he,hqh⟩
  have hh : (∑ q ∈ F.filter (fun q => q ∈ signedHead J), oddStarTerm c a q) ≤ V := by
    apply (sum_le_sum (g := fun q => oddStarTerm c b q) ?_).trans
      ((sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => oddStarTerm_nonneg c b q)).trans
        (hhead b (clamp_mem_signedCenters J a)))
    intro q hq
    have hq' := (mem_erase.mp (mem_filter.mp hq).1).1
    have hqb := (mem_erase.mp (hsub hq)).1
    have hgap := odd_gap_clamp (a:=a) (mem_filter.mp hq).2
    have hpos : 0 < |primitiveOddNumber q-primitiveOddNumber b| := by
      have h2 := odd_gap_ge_two hqb
      linarith
    exact div_le_div_of_nonneg_left (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
      hpos hgap
  have ht : (∑ q ∈ F.filter (fun q => q ∉ signedHead J), oddStarTerm c a q) ≤ T/2 := by
    calc
      _ ≤ ∑ q ∈ F.filter (fun q => q ∉ signedHead J), oddBinKernel c q/2 := by
        apply sum_le_sum
        intro q hq
        have hqa := (mem_erase.mp (mem_filter.mp hq).1).1
        exact div_le_div_of_nonneg_left (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
          (by norm_num) (odd_gap_ge_two hqa)
      _ ≤ _ := by
        simp only [div_eq_mul_inv,←sum_mul]
        exact mul_le_mul_of_nonneg_right ((signed_mass_tail F J hc hg).trans htail) (by norm_num)
  rw [← sum_filter_add_sum_filter_not F (fun q => q ∈ signedHead J) (oddStarTerm c a)]
  exact add_le_add hh ht

#print axioms signed_star_envelope
#print axioms signed_mass_tail
end OpenMathResearch.LongCycleExcedances
