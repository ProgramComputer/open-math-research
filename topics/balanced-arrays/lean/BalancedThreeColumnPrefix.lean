import OpenMathResearch.AlternatingSignRoots
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Exact prefix for the three-column balanced-array polynomial

The polynomial is defined by the once-normalized inclusion-exclusion formula.
Integer sign certificates use dyadic samples in the reflected variable.
-/

namespace BalancedThreeColumnPrefix

open Polynomial
open scoped BigOperators

/-- Once-normalized coefficient obtained by excluding common column entries. -/
def inclusionExclusion (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((n - j).choose (k - j) : ℤ) ^ 2

/-- Coefficient before or after restoring the binomial normalization. -/
def rowCoeff (original : Bool) (n k : ℕ) : ℤ :=
  (if original then (n.choose k : ℤ) else 1) * inclusionExclusion n k

/-- All coefficients up to the number of rows are included. -/
noncomputable def formulaRow (original : Bool) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (rowCoeff original n k : ℝ) * X ^ k

/-- The once-normalized polynomial. -/
noncomputable abbrev normalizedRow := formulaRow false

/-- The original polynomial reconstructed from the normalized formula. -/
noncomputable abbrev originalRow := formulaRow true

private def degreeBound (n : ℕ) : ℕ := 2 * n / 3

private def fastCoeff (original : Bool) (n k : ℕ) : ℤ :=
  (if original then (Nat.fast_choose n k : ℤ) else 1) *
    ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ j * (Nat.fast_choose k j : ℤ) *
        (Nat.fast_choose (n - j) (k - j) : ℤ) ^ 2

private theorem fastCoeff_eq (original : Bool) (n k : ℕ) :
    fastCoeff original n k = rowCoeff original n k := by
  simp only [fastCoeff, rowCoeff, inclusionExclusion, Nat.choose_eq_fast_choose]

private def scale : ℕ := 1048576

private def signNumerator (original : Bool) (n p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (degreeBound n + 1),
    fastCoeff original n k * (-(p : ℤ)) ^ k * (scale : ℤ) ^ (degreeBound n - k)

private def mesh : Bool → ℕ → List ℕ
  | false, 0 => [0]
  | false, 1 => [0]
  | false, 2 => [0, 360448]
  | false, 3 => [0, 139264, 4063232]
  | false, 4 => [0, 77824, 753664]
  | false, 5 => [0, 51200, 360448, 3670016]
  | false, 6 => [0, 36864, 221184, 1114112, 25165824]
  | false, 7 => [0, 27648, 155648, 557056, 3407872]
  | false, 8 => [0, 21504, 118784, 360448, 1310720, 13107200]
  | false, 9 => [0, 17408, 94208, 262144, 753664, 3276800, 75497472]
  | false, 10 => [0, 13824, 73728, 204800, 491520, 1507328, 8912896]
  | false, 11 => [0, 11776, 61440, 163840, 360448, 884736, 3145728, 31457280]
  | false, 12 => [0, 9728, 53248, 139264, 294912, 622592, 1638400, 7077888, 167772160]
  | false, 13 => [0, 8704, 45056, 114688, 229376, 458752, 1048576, 3145728, 18874368]
  | false, 14 => [0, 7424, 38912, 98304, 196608, 360448, 720896, 1769472, 6291456, 62914560]
  | false, 15 => [0, 6400, 34816, 86016, 163840, 294912, 557056, 1179648, 3014656, 13631488, 318767104]
  | false, 16 => [0, 5632, 29696, 73728, 147456, 253952, 442368, 851968, 1835008, 5505024, 33554432]
  | false, 17 => [0, 5120, 26624, 65536, 126976, 212992, 360448, 655360, 1245184, 3014656, 10485760, 109051904]
  | false, 18 => [0, 4608, 23552, 59392, 110592, 188416, 311296, 524288, 950272, 1900544, 5242880, 23068672, 536870912]
  | false, 19 => [0, 4096, 21504, 53248, 98304, 163840, 278528, 425984, 720896, 1376256, 3014656, 8912896, 54525952]
  | true, 0 => [0]
  | true, 1 => [0]
  | true, 2 => [0, 180224]
  | true, 3 => [0, 45056, 4194304]
  | true, 4 => [0, 18432, 557056]
  | true, 5 => [0, 9216, 188416, 3932160]
  | true, 6 => [0, 5376, 90112, 884736, 33554432]
  | true, 7 => [0, 3456, 49152, 360448, 3670016]
  | true, 8 => [0, 2304, 30720, 188416, 1179648, 17825792]
  | true, 9 => [0, 1600, 20480, 114688, 557056, 3538944, 117440512]
  | true, 10 => [0, 1216, 14336, 73728, 311296, 1441792, 11534336]
  | true, 11 => [0, 896, 10752, 51200, 196608, 720896, 3538944, 46137344]
  | true, 12 => [0, 704, 7936, 38912, 131072, 425984, 1638400, 9437184, 285212672]
  | true, 13 => [0, 544, 6144, 28672, 94208, 278528, 884736, 3538944, 27262976]
  | true, 14 => [0, 432, 4864, 21504, 69632, 196608, 557056, 1769472, 7864320, 96468992]
  | true, 15 => [0, 352, 3968, 17408, 53248, 147456, 376832, 1015808, 3538944, 18874368, 536870912]
  | true, 16 => [0, 304, 3200, 13824, 43008, 106496, 262144, 688128, 1900544, 7077888, 50331648]
  | true, 17 => [0, 248, 2688, 11264, 34816, 86016, 196608, 458752, 1179648, 3407872, 14680064, 176160768]
  | true, 18 => [0, 208, 2304, 9216, 27648, 69632, 155648, 344064, 786432, 2031616, 6291456, 33554432, 939524096]
  | true, 19 => [0, 176, 1920, 7680, 22528, 53248, 118784, 253952, 557056, 1310720, 3407872, 12058624, 88080384]
  | _, _ => []

private def Certificate (original : Bool) (n : ℕ) : Prop :=
  (mesh original n).length = degreeBound n + 1 ∧
  (mesh original n).Pairwise (· < ·) ∧
  fastCoeff original n (degreeBound n) ≠ 0 ∧
  (∀ k : Fin (n + 1), degreeBound n < k.val → fastCoeff original n k.val = 0) ∧
  ∀ i : Fin (mesh original n).length,
    0 < (-1 : ℤ) ^ i.val * signNumerator original n (mesh original n)[i.val]

private instance (original : Bool) (n : ℕ) : Decidable (Certificate original n) := by
  unfold Certificate
  infer_instance

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
private theorem checked (original : Bool) (n : Fin 20) : Certificate original n.val := by
  cases original <;> fin_cases n <;> decide

private theorem degreeBound_le (n : ℕ) : degreeBound n ≤ n := by
  unfold degreeBound
  omega

/-- Coefficient extraction from the explicit once-normalized polynomial. -/
theorem coeff_formulaRow (original : Bool) (n k : ℕ) :
    (formulaRow original n).coeff k = if k ≤ n then (rowCoeff original n k : ℝ) else 0 := by
  classical
  simp only [formulaRow, finset_sum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq,
    Finset.mem_range, Nat.lt_succ_iff]

/-- Both formula-defined prefix variants have exact degree ⌊2n/3⌋. -/
theorem formulaRow_natDegree_prefix (original : Bool) {n : ℕ} (hn : n < 20) :
    (formulaRow original n).natDegree = 2 * n / 3 := by
  change (formulaRow original n).natDegree = degreeBound n
  obtain ⟨_, _, hlead, htail, _⟩ := checked original ⟨n, hn⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_formulaRow]
    split
    · rename_i hkn
      have hz := htail ⟨k, Nat.lt_succ_iff.mpr hkn⟩ hk
      simpa [fastCoeff_eq] using congrArg (fun c : ℤ => (c : ℝ)) hz
    · rfl
  · simpa [coeff_formulaRow, degreeBound_le, fastCoeff_eq] using hlead

private theorem eval_truncated (original : Bool) {n : ℕ} (hn : n < 20) (x : ℝ) :
    (formulaRow original n).eval x =
      ∑ k ∈ Finset.range (degreeBound n + 1), (fastCoeff original n k : ℝ) * x ^ k := by
  have htail := (checked original ⟨n, hn⟩).2.2.2.1
  simp only [formulaRow, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, fastCoeff_eq]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (degreeBound_le n)))
  intro k hkn hk
  have hkD : degreeBound n < k := by
    simpa [Finset.mem_range, not_lt] using hk
  have hz : rowCoeff original n k = 0 :=
    (fastCoeff_eq original n k).symm.trans (htail ⟨k, Finset.mem_range.mp hkn⟩ hkD)
  simp [hz]

private theorem signNumerator_eq (original : Bool) {n : ℕ} (hn : n < 20) (p : ℕ) :
    (signNumerator original n p : ℝ) =
      (scale : ℝ) ^ degreeBound n * (formulaRow original n).eval (-(p : ℝ) / scale) := by
  rw [eval_truncated original hn, Finset.mul_sum]
  simp only [signNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  have hkD : k ≤ degreeBound n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (scale : ℝ) ^ degreeBound n =
      (scale : ℝ) ^ (degreeBound n - k) * (scale : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkD]
  rw [hpow, div_pow]
  have hscale : (scale : ℝ) ≠ 0 := by norm_num [scale]
  field_simp
  ring

/-- All roots of each formula-defined prefix row are simple and negative. -/
theorem prefix_formula_negative_roots (original : Bool) {n : ℕ} (hn : n < 20) :
    ∃ roots : Fin (2 * n / 3) → ℝ, StrictMono roots ∧ (∀ i, 0 < roots i) ∧
      (formulaRow original n).roots = (Finset.univ.image (fun i => -roots i)).val := by
  let G := (formulaRow original n).comp (-X)
  have hdegree : (formulaRow original n).natDegree = degreeBound n := formulaRow_natDegree_prefix original hn
  have hdegreeG : G.natDegree = degreeBound n := by
    simp [G, natDegree_comp, hdegree]
  obtain ⟨hlen, horder, hlead, _, hsign⟩ := checked original ⟨n, hn⟩
  let p (i : Fin (degreeBound n + 1)) : ℕ :=
    (mesh original n)[i.val]'(by rw [hlen]; exact i.isLt)
  let t (i : Fin (degreeBound n + 1)) : ℝ := (p i : ℝ) / scale
  have hscale : 0 < (scale : ℝ) := by norm_num [scale]
  have htp (i : Fin (degreeBound n + 1)) : 0 ≤ t i :=
    div_nonneg (Nat.cast_nonneg _) hscale.le
  have ht : StrictMono t := by
    intro i j hij
    apply div_lt_div_of_pos_right _ hscale
    exact_mod_cast (List.pairwise_iff_getElem.mp horder) i.val j.val
      (by rw [hlen]; exact i.isLt) (by rw [hlen]; exact j.isLt) hij
  have hs (i : Fin (degreeBound n + 1)) :
      0 < (-1 : ℝ) ^ i.val * G.eval (t i) := by
    have hInteger := hsign ⟨i.val, by rw [hlen]; exact i.isLt⟩
    have hp : 0 < (((-1 : ℤ) ^ i.val * signNumerator original n (p i) : ℤ) : ℝ) := by
      exact_mod_cast hInteger
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hp
    change 0 < (-1 : ℝ) ^ i.val * (signNumerator original n (p i) : ℝ) at hp
    rw [signNumerator_eq original hn] at hp
    rw [show -(p i : ℝ) / scale = -(t i) by rw [neg_div]] at hp
    simp only [G, eval_comp, eval_neg, eval_X]
    rw [← mul_left_comm] at hp
    exact pos_of_mul_pos_right hp (pow_nonneg hscale.le _)
  obtain ⟨roots, hmono, hbounds, hroots⟩ :=
    OpenMathResearch.AlternatingSignRoots.roots_of_alternating_sign_mesh G t hdegreeG ht hs
  have hpos i : 0 < roots i := (htp i.castSucc).trans_lt (hbounds i).1
  have hne : formulaRow original n ≠ 0 := by
    intro hzero
    have hcoeff : (formulaRow original n).coeff (degreeBound n) ≠ 0 := by
      simpa [coeff_formulaRow, degreeBound_le, fastCoeff_eq] using hlead
    exact hcoeff (by simp [hzero])
  have hr (i : Fin (degreeBound n)) : (formulaRow original n).IsRoot (-roots i) := by
    have hmem : roots i ∈ G.roots := by
      rw [hroots]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa [G, eval_comp, Polynomial.IsRoot] using (mem_roots'.mp hmem).2
  exact ⟨roots, hmono, hpos,
    OpenMathResearch.AlternatingSignRoots.roots_of_complete_list
      (formulaRow original n) (fun i => -roots i) hdegree hne
      (neg_injective.comp hmono.injective) hr⟩

/-- Explicit coefficients of the normalized polynomial through its full row count. -/
theorem coeff_normalizedRow (n k : ℕ) :
    (normalizedRow n).coeff k = if k ≤ n then (inclusionExclusion n k : ℝ) else 0 := by
  simpa [rowCoeff] using coeff_formulaRow false n k

/-- Restoring the binomial factor recovers the original formula coefficients. -/
theorem coeff_originalRow (n k : ℕ) :
    (originalRow n).coeff k =
      if k ≤ n then (n.choose k : ℝ) * (inclusionExclusion n k : ℝ) else 0 := by
  simpa [rowCoeff] using coeff_formulaRow true n k

/-- All roots of the once-normalized prefix rows are simple and negative. -/
theorem prefix_negative_roots {n : ℕ} (hn : n < 20) :
    ∃ roots : Fin (2 * n / 3) → ℝ, StrictMono roots ∧ (∀ i, 0 < roots i) ∧
      (normalizedRow n).roots = (Finset.univ.image (fun i => -roots i)).val :=
  prefix_formula_negative_roots false hn

/-- All roots of the original formula-defined prefix rows are simple and negative. -/
theorem prefix_original_negative_roots {n : ℕ} (hn : n < 20) :
    ∃ roots : Fin (2 * n / 3) → ℝ, StrictMono roots ∧ (∀ i, 0 < roots i) ∧
      (originalRow n).roots = (Finset.univ.image (fun i => -roots i)).val :=
  prefix_formula_negative_roots true hn

end BalancedThreeColumnPrefix
