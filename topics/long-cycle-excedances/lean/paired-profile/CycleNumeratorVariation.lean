import RepositoryOrbitBaseline

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open Finset

/-- The cutoff weights omit the constant one from the probability series. -/
def cutoffWeight (k : ℕ) (d : ℕ → ℝ) (s : ℕ) : ℝ := if k ≤ s then d s else 0

def numeratorDiff (k : ℕ) (d : ℕ → ℝ) (s : ℕ) : ℝ :=
  cutoffWeight k d s - cutoffWeight k d (s-1)

theorem numeratorDiff_below {k s : ℕ} (d : ℕ → ℝ) (hs : s < k) :
    numeratorDiff k d s = 0 := by
  simp only [numeratorDiff,cutoffWeight,if_neg (not_le_of_gt hs),
    if_neg (by omega : ¬k ≤ s-1),sub_zero]

theorem Spec.numeratorDiff_at_cutoff {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) :
    numeratorDiff k d k = 1/(k:ℝ) := by
  simp only [numeratorDiff,cutoffWeight,if_pos le_rfl,if_neg (by omega : ¬k ≤ k-1),sub_zero]
  exact one_cycle h le_rfl (by omega)

theorem Spec.mul_numeratorDiff {k s : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hs : k < s) :
    (s:ℝ)*numeratorDiff k d s = d (s-k)-d (s-1) := by
  have he := adjacent h hs
  rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] at he
  simp only [numeratorDiff,cutoffWeight,if_pos hs.le,if_pos (by omega : k ≤ s-1)]
  linarith only [he]

/-- The whole open first block has negative signed reciprocal differences. -/
theorem Spec.numeratorDiff_between {k s : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    (hks : k < s) (hs : s < 2*k) :
    numeratorDiff k d s = -1/((s:ℝ)*((s:ℝ)-1)) := by
  have hs' : (1:ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  rw [numeratorDiff,cutoffWeight,cutoffWeight,if_pos hks.le,if_pos (by omega : k ≤ s-1),
    one_cycle h hks.le hs,one_cycle h (by omega : k ≤ s-1) (by omega),
    Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one]
  field_simp [show (s:ℝ) ≠ 0 by positivity,(sub_pos.mpr hs').ne'] <;> ring

theorem Spec.abs_numeratorDiff_between {k s : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    (hks : k < s) (hs : s < 2*k) :
    |numeratorDiff k d s| = 1/((s:ℝ)*((s:ℝ)-1)) := by
  rw [h.numeratorDiff_between hks hs,neg_div,abs_neg]
  have h1 : (1:ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  exact abs_of_nonneg (div_nonneg (by norm_num) (mul_nonneg (by positivity) (sub_nonneg.mpr h1.le)))

/-- The isolated jump at the start of the two-cycle range. -/
theorem Spec.numeratorDiff_at_twice {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) :
    numeratorDiff k d (2*k) = (1/(k:ℝ)-1/(2*(k:ℝ)-1))/(2*(k:ℝ)) := by
  have hd := h.mul_numeratorDiff (show k < 2*k by omega)
  have h2k : (0:ℝ) < 2*(k:ℝ) := by positivity
  rw [show 2*k-k=k by omega,one_cycle h le_rfl (by omega : k < 2*k),
    one_cycle h (by omega : k ≤ 2*k-1) (by omega)] at hd
  rw [Nat.cast_sub (by omega : 1 ≤ 2*k),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hd
  exact (eq_div_iff h2k.ne').mpr (by linarith only [hd])

private theorem reciprocal_width_lt {k : ℕ} (hk : 0 < k) :
    1/(k:ℝ)-1/(2*(k:ℝ)-1) < 1/(2*(k:ℝ)) := by
  have hk0 : (0:ℝ) < k := by positivity
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < 2*(k:ℝ)-1 := by linarith only [hk1]
  have hl : 1/(2*(k:ℝ)) < 1/(2*(k:ℝ)-1) :=
    div_lt_div_of_pos_left (by norm_num) hp (by linarith)
  have he : 1/(k:ℝ)-1/(2*(k:ℝ)) = 1/(2*(k:ℝ)) := by
    field_simp [hk0.ne'] <;> ring
  linarith only [hl,he]

theorem Spec.numeratorDiff_at_twice_pos_lt {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 2 ≤ k) :
    0 < numeratorDiff k d (2*k) ∧ numeratorDiff k d (2*k) < 1/(4*(k:ℝ)^2) := by
  have hk' : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (0:ℝ) < k := by positivity
  have hp : 0 < 2*(k:ℝ) := by positivity
  rw [h.numeratorDiff_at_twice (by omega)]
  constructor
  · apply div_pos _ hp
    exact sub_pos.mpr (div_lt_div_of_pos_left (by norm_num) hk0 (by linarith only [hk']))
  · apply (div_lt_iff₀ hp).mpr
    have he : 1/(4*(k:ℝ)^2)*(2*(k:ℝ)) = 1/(2*(k:ℝ)) := by field_simp [hk0.ne'] <;> ring
    rw [he]
    exact reciprocal_width_lt (by omega : 0 < k)

private theorem sum_Ico_backward_sub (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Ico a b, (f i - f (i-1))) = f (b-1)-f (a-1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ico_succ_top hb,ih,Nat.add_sub_cancel]
    ring

/-- Once the lag is past the atom, the recurrence is a short telescoping sum. -/
theorem Spec.mul_numeratorDiff_eq_neg_sum {k s : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    (hk : 0 < k) (hs : 2*k < s) :
    (s:ℝ)*numeratorDiff k d s = -∑ i ∈ Ico (s-k+1) s, numeratorDiff k d i := by
  rw [h.mul_numeratorDiff (by omega : k < s)]
  unfold numeratorDiff
  rw [sum_Ico_backward_sub (cutoffWeight k d) (by omega : s-k+1 ≤ s)]
  simp only [Nat.add_sub_cancel,cutoffWeight,if_pos (by omega : k ≤ s-1),
    if_pos (by omega : k ≤ s-k)]
  ring

/-- The variation within the first block telescopes to its endpoint gap. -/
theorem Spec.first_block_variation {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) :
    (∑ s ∈ Ico (k+1) (2*k), |numeratorDiff k d s|) = 1/(k:ℝ)-1/(2*(k:ℝ)-1) := by
  have he : (∑ s ∈ Ico (k+1) (2*k), |numeratorDiff k d s|) =
      -∑ s ∈ Ico (k+1) (2*k), numeratorDiff k d s := by
    rw [←sum_neg_distrib]
    apply sum_congr rfl
    intro s hs
    have hks : k < s := by have := (mem_Ico.mp hs).1; omega
    have hs1 : (1:ℝ) < s := by exact_mod_cast (show 1 < s by omega)
    apply abs_of_nonpos
    rw [h.numeratorDiff_between hks (mem_Ico.mp hs).2,neg_div]
    exact neg_nonpos.mpr (div_nonneg (by norm_num)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hs1.le)))
  rw [he]
  unfold numeratorDiff
  rw [sum_Ico_backward_sub (cutoffWeight k d) (by omega : k+1 ≤ 2*k)]
  simp only [Nat.add_sub_cancel,cutoffWeight,if_pos le_rfl,if_pos (by omega : k ≤ 2*k-1)]
  rw [one_cycle h le_rfl (by omega : k < 2*k),
    one_cycle h (by omega : k ≤ 2*k-1) (by omega),Nat.cast_sub (by omega : 1 ≤ 2*k),
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

private def numeratorBlockBound (k j : ℕ) : ℝ :=
  1/(2*(j.factorial:ℝ)*(k:ℝ)^2)

private theorem numeratorBlockBound_scale {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    (j:ℝ)*numeratorBlockBound k j = numeratorBlockBound k (j-1) := by
  have h : j.factorial=j*(j-1).factorial := calc
    _ = ((j-1)+1).factorial := by rw [Nat.sub_add_cancel hj]
    _ = ((j-1)+1)*(j-1).factorial := Nat.factorial_succ _
    _ = _ := by rw [Nat.sub_add_cancel hj]
  have hf : (j.factorial:ℝ) = (j:ℝ)*((j-1).factorial:ℝ) := by exact_mod_cast h
  have hf0 : (0:ℝ) < ((j-1).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos (j-1)
  unfold numeratorBlockBound
  rw [hf]
  field_simp [show (k:ℝ) ≠ 0 by positivity, show (j:ℝ) ≠ 0 by positivity,hf0.ne'] <;> ring

private theorem Spec.numeratorDiff_second_block {k s : ℕ} {d : ℕ → ℝ}
    (h : Spec k d) (hk : 0 < k) (hs : 2*k < s) :
    |numeratorDiff k d s| ≤ numeratorBlockBound k 2 := by
  have h1 := h.reciprocal_bounds hk (p:=s-k) (by omega)
  have h2 := h.reciprocal_bounds hk (p:=s-1) (by omega)
  have hh : |d (s-k)-d (s-1)| ≤ 1/(k:ℝ)-1/(2*(k:ℝ)-1) := by
    apply abs_le.mpr
    constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2]
  have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hk0 : (0:ℝ) < k := by positivity
  have hsk : 2*(k:ℝ) ≤ s := by exact_mod_cast hs.le
  have hscaled : (s:ℝ)*|numeratorDiff k d s| ≤ 1/(2*(k:ℝ)) := by
    rw [←abs_of_pos hs0,←abs_mul,h.mul_numeratorDiff (by omega : k < s)]
    exact hh.trans (reciprocal_width_lt hk).le
  have hpos : 0 ≤ numeratorBlockBound k 2 := by unfold numeratorBlockBound; positivity
  have he : (2*(k:ℝ))*numeratorBlockBound k 2 = 1/(2*(k:ℝ)) := by
    norm_num [numeratorBlockBound,Nat.factorial]
    field_simp [hk0.ne'] <;> ring
  rw [←he] at hscaled
  have hm := hscaled.trans (mul_le_mul_of_nonneg_right hsk hpos)
  by_contra! hbad
  exact (not_lt_of_ge hm) (mul_lt_mul_of_pos_left hbad hs0)

/-- The previous block covers early lags and strong induction covers lags
in the same block. Both fit the previous block's bound. -/
theorem Spec.numeratorDiff_factorial_block {k j s : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    (hk : 0 < k) (hj : 2 ≤ j) (hlo : j*k < s) (hhi : s ≤ (j+1)*k) :
    |numeratorDiff k d s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2) := by
  change |numeratorDiff k d s| ≤ numeratorBlockBound k j
  induction s using Nat.strong_induction_on generalizing j with
  | h s ih =>
    have hs : 2*k < s := (Nat.mul_le_mul_right k hj).trans_lt hlo
    by_cases hj2 : j = 2
    · subst j
      exact h.numeratorDiff_second_block hk hs
    have hprev : 2 ≤ j-1 := by omega
    have hadd : j = (j-1)+1 := (Nat.sub_add_cancel (by omega : 1 ≤ j)).symm
    have hprod : j*k = (j-1)*k+k := by
      calc
        _ = ((j-1)+1)*k := congrArg (·*k) hadd
        _ = _ := by rw [Nat.add_mul,Nat.one_mul]
    have hscale := numeratorBlockBound_scale hk (by omega : 0 < j)
    have hpos : 0 ≤ numeratorBlockBound k j := by unfold numeratorBlockBound; positivity
    have hmono : numeratorBlockBound k j ≤ numeratorBlockBound k (j-1) := by
      rw [←hscale,←one_mul (numeratorBlockBound k j)]
      have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hj1 hpos
    have hi (i : ℕ) (hi' : i ∈ Ico (s-k+1) s) :
        |numeratorDiff k d i| ≤ numeratorBlockBound k (j-1) := by
      obtain ⟨hil,hir⟩ := mem_Ico.mp hi'
      by_cases hip : i ≤ j*k
      · apply ih i hir hprev (by omega)
        rw [←hadd]
        exact hip
      · exact (ih i hir hj (lt_of_not_ge hip) (hir.le.trans hhi)).trans hmono
    have hsum : (∑ i ∈ Ico (s-k+1) s, |numeratorDiff k d i|) ≤
        ((k-1:ℕ):ℝ)*numeratorBlockBound k (j-1) := by
      calc
        _ ≤ ∑ _i ∈ Ico (s-k+1) s, numeratorBlockBound k (j-1) :=
          sum_le_sum (fun i hi' => hi i hi')
        _ = _ := by
          rw [sum_const,nsmul_eq_mul,Nat.card_Ico,show s-(s-k+1)=k-1 by omega]
    have hsk : (j:ℝ)*(k:ℝ) ≤ s := by exact_mod_cast hlo.le
    have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    suffices hh : (s:ℝ)*|numeratorDiff k d s| ≤ (s:ℝ)*numeratorBlockBound k j by
      by_contra! hbad
      exact (not_lt_of_ge hh) (mul_lt_mul_of_pos_left hbad hs0)
    calc
      _ = |(s:ℝ)*numeratorDiff k d s| := by rw [abs_mul,abs_of_pos hs0]
      _ ≤ ∑ i ∈ Ico (s-k+1) s, |numeratorDiff k d i| := by
        rw [h.mul_numeratorDiff_eq_neg_sum hk hs,abs_neg]
        exact abs_sum_le_sum_abs _ _
      _ ≤ (k:ℝ)*numeratorBlockBound k (j-1) := hsum.trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1)
          (by unfold numeratorBlockBound; positivity))
      _ = ((j:ℝ)*(k:ℝ))*numeratorBlockBound k j := by rw [←hscale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsk hpos

#print axioms Spec.numeratorDiff_at_cutoff
#print axioms Spec.numeratorDiff_between
#print axioms Spec.numeratorDiff_at_twice
#print axioms Spec.numeratorDiff_at_twice_pos_lt
#print axioms Spec.mul_numeratorDiff_eq_neg_sum
#print axioms Spec.first_block_variation
#print axioms Spec.numeratorDiff_factorial_block
end OpenMathResearch.LongCycleExcedances.CycleProbability
