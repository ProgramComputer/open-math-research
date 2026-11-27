import CenteredBinGeometry
import PrincipalHarmonic

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability Finset Real

theorem numerator_block_atom_size {k h i : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k)
    (hh : 1 ≤ h) (hi : i < k) :
    |numeratorDiff k d (h*k+i+1)| ≤ 1/((h.factorial:ℝ)*(k:ℝ)^2) := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hs : h*k+i+1 ≤ (h+1)*k := by rw [Nat.add_mul,Nat.one_mul]; omega
  by_cases h1 : h=1
  · subst h
    simp only [Nat.one_mul,Nat.factorial_one,Nat.cast_one,one_mul]
    by_cases he : k+i+1=2*k
    · rw [he,abs_of_pos (hd.numeratorDiff_at_twice_pos_lt hk).1]
      apply (hd.numeratorDiff_at_twice_pos_lt hk).2.le.trans
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [sq_nonneg (k:ℝ)]
    · have hmid : k+i+1 < 2*k := by omega
      rw [hd.abs_numeratorDiff_between (by omega) hmid]
      apply one_div_le_one_div_of_le (by positivity)
      have hcast : (k:ℝ)+1 ≤ (k+i+1:ℕ) := by exact_mod_cast (show k+1 ≤ k+i+1 by omega)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hcast) hk0.le,
        mul_nonneg (sub_nonneg.mpr hcast) (sub_nonneg.mpr hcast), hk0]
  · apply (hd.numeratorDiff_factorial_block (by omega) (by omega : 2 ≤ h) (by omega) hs).trans
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [show 0 ≤ (h.factorial:ℝ)*(k:ℝ)^2 by positivity]

private theorem bin_power_bound {k h i : ℕ} (hk : 0 < k) (hi : i < k) :
    (9/8:ℝ)^degreeBin k (h*k+i+1) ≤ (2:ℝ)^(h+1) := by
  have hs : h*k+i+1 ≤ (h+1)*k := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hb : degreeBin k (h*k+i+1) ≤ 4*(h+1) := by
    unfold degreeBin
    apply Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hk).mpr ?_)
    have hpos : 1 ≤ 4*(h*k+i+1)+k := by omega
    have he := Nat.sub_add_cancel hpos
    nlinarith
  calc
    _ ≤ (9/8:ℝ)^(4*(h+1)) := pow_le_pow_right₀ (by norm_num) hb
    _ = ((9/8:ℝ)^4)^(h+1) := pow_mul .. 
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _

private theorem block_tilt_bound {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k) (h : ℕ) :
    (∑ i ∈ range k, (k:ℝ)*|numeratorDiff k d (h*k+i+1)| *(9/8:ℝ)^degreeBin k (h*k+i+1))
      ≤ (2:ℝ)^(h+1)/h.factorial := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  by_cases he : h=0
  · subst h
    simp only [Nat.zero_mul,Nat.zero_add,Nat.factorial_zero,Nat.cast_one,div_one]
    rw [sum_eq_single_of_mem (k-1) (mem_range.mpr (by omega))]
    · have hidx : k-1+1=k := by omega
      rw [hidx,hd.numeratorDiff_at_cutoff (by omega), abs_of_pos (by positivity)]
      have hp := bin_power_bound (h:=0) (show 0 < k by omega) (show k-1 < k by omega)
      simpa [hidx,hk0.ne'] using hp
    · intro i hi hn
      have hlt : i+1 < k := by have := mem_range.mp hi; omega
      simp [numeratorDiff_below d hlt]
  · have hterm (i : ℕ) (hi : i ∈ range k) :
        (k:ℝ)*|numeratorDiff k d (h*k+i+1)| *(9/8:ℝ)^degreeBin k (h*k+i+1) ≤
          (k:ℝ)*(1/((h.factorial:ℝ)*(k:ℝ)^2))*2^(h+1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (numerator_block_atom_size hd hk (by omega) (mem_range.mp hi)) hk0.le)
        (bin_power_bound (by omega) (mem_range.mp hi)) (by positivity) (by positivity)
    apply (sum_le_sum hterm).trans_eq
    simp only [sum_const,card_range,nsmul_eq_mul]
    field_simp <;> ring

/-- A single tilted absolute numerator bound suffices for every principal
truncation. It retains the isolated atom at the minimum cycle length. -/
theorem tilted_numerator_mass {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k) (N : ℕ) :
    (∑ s ∈ Icc k N, (k:ℝ)*|numeratorDiff k d s| *(9/8:ℝ)^degreeBin k s) < 16 := by
  let f (s:ℕ) := (k:ℝ)*|numeratorDiff k d s| *(9/8:ℝ)^degreeBin k s
  have hf (s:ℕ) : 0 ≤ f s := by dsimp [f]; positivity
  have hwalk (H : ℕ) : (∑ s ∈ range (H*k), f (s+1)) ≤
      ∑ h ∈ range H, (2:ℝ)^(h+1)/h.factorial := by
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Nat.succ_mul,sum_range_add,sum_range_succ]
      exact add_le_add ih (block_tilt_bound hd hk H)
  have hs : Icc k N ⊆ range ((N+1)*k+1) := by
    intro s h
    apply mem_range.mpr
    have := (mem_Icc.mp h).2
    nlinarith
  have hsum := sum_le_sum_of_subset_of_nonneg (f:=f) hs (fun i _ _ => hf i)
  rw [sum_range_succ' f] at hsum
  have hzero : f 0=0 := by simp [f,numeratorDiff_below d (by omega : 0 < k)]
  rw [hzero,add_zero] at hsum
  apply (hsum.trans (hwalk (N+1))).trans_lt
  have hh := (NormedSpace.expSeries_div_hasSum_exp (2:ℝ)).mul_left (2:ℝ)
  have hu := hh.summable.sum_le_tsum (range (N+1)) (fun h _ => by positivity)
  rw [hh.tsum_eq] at hu
  have heq (h : ℕ) : (2:ℝ)^(h+1)/h.factorial=2*((2:ℝ)^h/h.factorial) := by rw [pow_succ]; ring
  simp_rw [heq]
  apply hu.trans_lt
  rw [Real.exp_eq_exp_ℝ.symm]
  have h1 : exp 1 < (11/4:ℝ) := by linarith only [exp_one_lt_d9]
  have h2 := pow_lt_pow_left₀ h1 (exp_pos _).le (by decide : (2:ℕ)≠0)
  rw [←exp_nat_mul,mul_one] at h2
  norm_num at h2
  linarith

#print axioms tilted_numerator_mass
end OpenMathResearch.LongCycleExcedances
