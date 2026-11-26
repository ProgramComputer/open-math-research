import OpenMathResearch.DiskUniqueness
import LongCycleMixedRootWitnesses
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OpenMathResearch.LongCycleExcedances

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- The evaluation using exactly the retained low coefficients of a reduced row. -/
def prefixEval (P : ℝ[X]) (W : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ range W, P.coeff j * (-y) ^ j

def tailRatio (N W : ℕ) (B : ℝ) : ℝ :=
  B * (((W : ℝ) + 2) / ((W : ℝ) + 1)) ^ N

def tailBound (N W : ℕ) (B : ℝ) : ℝ :=
  ((W : ℝ) + 1) ^ N * B ^ W / (1 - tailRatio N W B)

private def tailMonomial (N W : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  ((W : ℝ) + 1 + j) ^ N * B ^ (W + j)

private theorem tailMonomial_step (N W : ℕ) {B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    tailMonomial N W B (j+1) ≤ tailRatio N W B * tailMonomial N W B j := by
  have hW : 0 < ((W : ℝ) + 1) := by positivity
  have hbase : (W : ℝ) + 1 + (j + 1 : ℕ) ≤
      (((W : ℝ) + 2) / ((W : ℝ) + 1)) * ((W : ℝ) + 1 + j) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hW).2
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hp := pow_le_pow_left₀ (show 0 ≤ (W : ℝ) + 1 + (j+1 : ℕ) by positivity) hbase N
  unfold tailMonomial tailRatio
  calc
    _ ≤ ((((W : ℝ) + 2) / ((W : ℝ) + 1)) * ((W : ℝ) + 1 + j)) ^ N *
        B ^ (W + (j+1)) := mul_le_mul_of_nonneg_right hp (pow_nonneg hB _)
    _ = _ := by rw [mul_pow, ← Nat.add_assoc, pow_succ]; ring

/-- The omitted term at exponent j of E_N/t is bounded by (j+1)^N.
Bounding the entire omitted part uses the certificate's same ratio and tail. -/
theorem abs_eval_sub_prefix_le_tail (P : ℝ[X]) (N W : ℕ) {y B : ℝ}
    (hy : 0 ≤ y) (hyB : y ≤ B) (hq : tailRatio N W B < 1)
    (hcoeff : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N) :
    |P.eval (-y) - prefixEval P W y| ≤ tailBound N W B := by
  let M := P.natDegree + 1
  have hdegree : P.natDegree < W + M := by dsimp [M]; omega
  have hB : 0 ≤ B := hy.trans hyB
  have hq0 : 0 ≤ tailRatio N W B := by unfold tailRatio; positivity
  rw [Polynomial.eval_eq_sum_range' hdegree, Finset.sum_range_add, prefixEval, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ range M, |P.coeff (W+i) * (-y) ^ (W+i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range M, tailMonomial N W B i := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨hc0, hc⟩ := hcoeff (W+i) (by omega)
      rw [abs_mul, abs_of_nonneg hc0, abs_pow, abs_neg, abs_of_nonneg hy]
      unfold tailMonomial
      push_cast at hc
      rw [add_right_comm] at hc
      exact mul_le_mul hc (pow_le_pow_left₀ hy hyB _) (pow_nonneg hy _) (by positivity)
    _ ≤ _ := by
      unfold tailBound
      exact DiskUniqueness.geometric_tail_bound (tailMonomial N W B)
        (((W : ℝ) + 1) ^ N * B ^ W) (tailRatio N W B) hq0 hq
        (by simp [tailMonomial]) (by positivity) (tailMonomial_step N W hB) M

/-- A strict signed margin for the prefix transfers to the whole polynomial.
Use this at the dyadic endpoints of an intermediate certificate window. -/
theorem signed_eval_pos_of_prefix_margin (P : ℝ[X]) (N W : ℕ) {y B σ : ℝ}
    (hy : 0 ≤ y) (hyB : y ≤ B) (hq : tailRatio N W B < 1)
    (hcoeff : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N)
    (hσ : |σ| = 1) (hmargin : tailBound N W B < σ * prefixEval P W y) :
    0 < σ * P.eval (-y) := by
  have ht := abs_eval_sub_prefix_le_tail P N W hy hyB hq hcoeff
  have hmul : |σ * (P.eval (-y) - prefixEval P W y)| ≤ tailBound N W B := by
    rw [abs_mul, hσ, one_mul]
    exact ht
  have hl := (abs_le.mp hmul).1
  rw [mul_sub] at hl
  linarith

/-- An exact endpoint value separated from zero by its omitted-term bound. -/
def PrefixMargin (P : ℝ[X]) (N W : ℕ) (y σ : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ y ∧ y ≤ B ∧ tailRatio N W B < 1 ∧
    tailBound N W B < σ * prefixEval P W y

private theorem PrefixMargin.signed_pos {P : ℝ[X]} {N W : ℕ} {y σ : ℝ}
    (h : PrefixMargin P N W y σ)
    (hcoeff : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N)
    (hσ : |σ| = 1) : 0 < σ * P.eval (-y) := by
  obtain ⟨B, hy, hyB, hq, hm⟩ := h
  exact signed_eval_pos_of_prefix_margin P N W hy hyB hq hcoeff hσ hm

private theorem old_product_neg_of_margins {P : ℝ[X]} {N W : ℕ} {a b σ : ℝ}
    (ha : PrefixMargin P N W a σ) (hb : PrefixMargin P N W b (-σ))
    (hcoeff : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N)
    (hσ : |σ| = 1) : P.eval (-a) * P.eval (-b) < 0 := by
  have hx := ha.signed_pos hcoeff hσ
  have hy := hb.signed_pos hcoeff (by simpa)
  have hsq : σ ^ 2 = 1 := by rw [← sq_abs, hσ]; norm_num
  nlinarith only [mul_pos hx hy, congrArg (fun x : ℝ => x * P.eval (-a) * P.eval (-b)) hsq]

/-- The mixed-root theorem can use exact prefix certificates at either endpoint
of a strict bracket. Exact point witnesses and already proved signs can be combined
with those certificates. -/
theorem interlace_of_prefix_and_mixed_witnesses {m N W : ℕ} {P Q : ℝ[X]}
    (l u : Fin m → ℝ) (hP : P ≠ 0) (hdegP : P.natDegree = m)
    (hdegQ : Q.natDegree = m + 1) (hzero : 0 < Q.eval 0)
    (hlead : 0 < Q.leadingCoeff) (hpos : ∀ i, 0 < l i)
    (horder : ∀ i j, i < j → u i < l j)
    (hcoeffP : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N)
    (hcoeffQ : ∀ j ≥ W, 0 ≤ Q.coeff j ∧ Q.coeff j ≤ ((j : ℝ) + 1) ^ (N+1))
    (hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ (P.eval (-l i) * P.eval (-u i) < 0 ∨
        (PrefixMargin P N W (l i) ((-1 : ℝ) ^ i.val) ∧
          PrefixMargin P N W (u i) (-((-1 : ℝ) ^ i.val))))))
    (hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val+1) * Q.eval (-l i) ∨
      PrefixMargin Q (N+1) W (l i) ((-1 : ℝ) ^ (i.val+1)))
    (hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val+1) * Q.eval (-u i) ∨
      PrefixMargin Q (N+1) W (u i) ((-1 : ℝ) ^ (i.val+1))) :
    ∃ (old : Fin m → ℝ) (next : Fin (m + 1) → ℝ),
      OrientedNegativeInterlace.CompleteNegativeRoots P old ∧
      OrientedNegativeInterlace.CompleteNegativeRoots Q next ∧
      ∀ i, next i.castSucc < l i ∧ l i ≤ old i ∧ old i ≤ u i ∧ u i < next i.succ := by
  apply interlace_of_mixed_root_witnesses l u hP hdegP hdegQ hzero hlead hpos horder
  · intro i
    rcases hold i with hpoint | ⟨hwidth, hproduct | ⟨hl, hu⟩⟩
    · exact Or.inl hpoint
    · exact Or.inr ⟨hwidth, hproduct⟩
    · exact Or.inr ⟨hwidth, old_product_neg_of_margins hl hu hcoeffP (by simp [abs_pow])⟩
  · intro i
    exact (hsLeft i).elim id (fun hm => hm.signed_pos hcoeffQ (by simp [abs_pow]))
  · intro i
    exact (hsRight i).elim id (fun hm => hm.signed_pos hcoeffQ (by simp [abs_pow]))

/-- Interval Horner arithmetic for a nonnegative real input. The interval is
closed and the endpoints of each partial evaluation are rounded only by the
arithmetic used to supply the certificate. -/
def intervalHorner (a b : ℝ) : ℕ → (ℕ → ℝ) → ℝ × ℝ
  | 0, _ => (0, 0)
  | W+1, c =>
    let ends := intervalHorner a b W (fun j => c (j+1))
    (c 0 + min (a * ends.1) (b * ends.1),
      c 0 + max (a * ends.2) (b * ends.2))

private theorem mul_value_between {a b y t L U : ℝ}
    (ha : 0 ≤ a) (hay : a ≤ y) (hyb : y ≤ b) (hl : L ≤ t) (hu : t ≤ U) :
    min (a * L) (b * L) ≤ y * t ∧ y * t ≤ max (a * U) (b * U) := by
  have hy := ha.trans hay
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_left hl hy)
    by_cases hL : 0 ≤ L
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hay hL)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hyb (le_of_not_ge hL))
  · apply le_trans (mul_le_mul_of_nonneg_left hu hy)
    by_cases hU : 0 ≤ U
    · exact (mul_le_mul_of_nonneg_right hyb hU).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hay (le_of_not_ge hU)).trans (le_max_left _ _)

theorem intervalHorner_sound {a b y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hyb : y ≤ b)
    (W : ℕ) (c : ℕ → ℝ) :
    (intervalHorner a b W c).1 ≤ (∑ j ∈ range W, c j * y^j) ∧
      (∑ j ∈ range W, c j * y^j) ≤ (intervalHorner a b W c).2 := by
  induction W generalizing c with
  | zero => simp [intervalHorner]
  | succ W ih =>
    have heq : (∑ j ∈ range (W+1), c j * y^j) =
        c 0 + y * (∑ j ∈ range W, c (j+1) * y^j) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm (c 0)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [heq]
    obtain ⟨hl, hu⟩ := ih (fun j => c (j+1))
    obtain ⟨hlo, hhi⟩ := mul_value_between ha hay hyb hl hu
    exact ⟨add_le_add_left hlo _, add_le_add_left hhi _⟩

/-- Exact interval arithmetic with a signed prefix and its geometric omitted
tail certifies the whole-row sign throughout a nonnegative modulus interval. -/
theorem signed_pos_on_window_of_horner (P : ℝ[X]) (N W : ℕ) {a b B σ : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ B) (hq : tailRatio N W B < 1)
    (hcoeff : ∀ j ≥ W, 0 ≤ P.coeff j ∧ P.coeff j ≤ ((j : ℝ) + 1) ^ N)
    (hσ : |σ| = 1)
    (hmargin : tailBound N W B <
      (intervalHorner a b W (fun j => σ * ((-1 : ℝ)^j * P.coeff j))).1) :
    ∀ y ∈ Set.Icc a b, 0 < σ * P.eval (-y) := by
  intro y hy
  have heq : (∑ j ∈ range W, σ * ((-1 : ℝ)^j * P.coeff j) * y^j) =
      σ * prefixEval P W y := by
    rw [prefixEval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show -y = (-1 : ℝ) * y by ring, mul_pow]
    ring
  have hl := (intervalHorner_sound ha hy.1 hy.2 W (fun j => σ * ((-1 : ℝ)^j * P.coeff j))).1
  rw [heq] at hl
  exact signed_eval_pos_of_prefix_margin P N W (ha.trans hy.1) (hy.2.trans hb)
    hq hcoeff hσ (hmargin.trans_le hl)

#print axioms signed_pos_on_window_of_horner

private def rowFromCoeffs (D : ℕ) (a : ℕ → ℕ) : ℝ[X] :=
  ∑ j ∈ range D, C (a j : ℝ) * X ^ j

private theorem coeff_rowFromCoeffs (D : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    (rowFromCoeffs D a).coeff j = if j < D then (a j : ℝ) else 0 := by
  simp [rowFromCoeffs, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow,
    Finset.sum_ite_eq', Finset.mem_range]

private def quotient14Coeff : ℕ → ℕ
  | 0 => 1
  | 1 => 9894
  | 2 => 1675350
  | 3 => 52145198
  | 4 => 483396447
  | 5 => 1721401644
  | 6 => 2599338132
  | 7 => 1721401644
  | 8 => 483396447
  | 9 => 52145198
  | 10 => 1675350
  | 11 => 9894
  | 12 => 1
  | _ => 0

private def quotient15Coeff : ℕ → ℕ
  | 0 => 1
  | 1 => 22804
  | 2 => 5676309
  | 3 => 252033641
  | 4 => 3259289750
  | 5 => 16285228533
  | 6 => 35462558562
  | 7 => 35462558562
  | 8 => 16285228533
  | 9 => 3259289750
  | 10 => 252033641
  | 11 => 5676309
  | 12 => 22804
  | 13 => 1
  | _ => 0

/-- Exact cycle-decomposition coefficient vectors at sizes 14 and 15 for
cutoff seven. Their derivation from the original rows is recorded separately. -/
def quotient14At7 : ℝ[X] := rowFromCoeffs 13 quotient14Coeff

def quotient15At7 : ℝ[X] := rowFromCoeffs 14 quotient15Coeff

private theorem quotient15At7_tail : ∀ j ≥ 4, 0 ≤ quotient15At7.coeff j ∧ quotient15At7.coeff j ≤ ((j : ℝ) + 1) ^ 15 := by
  intro j hj
  rw [quotient15At7, coeff_rowFromCoeffs]
  split
  · rename_i h
    interval_cases j <;> norm_num [quotient15Coeff]
  · exact ⟨le_rfl, by positivity⟩

/-- The first separating window for the cutoff-seven cycle rows at sizes
14 and 15, checked from only four low coefficients and the geometric tail. -/
theorem cutoff7_first_window_14_15 :
    quotient14At7.eval (-(6 / 65536 : ℝ)) * quotient14At7.eval (-(7 / 65536 : ℝ)) < 0 ∧
    quotient15At7.eval (-(6 / 65536 : ℝ)) < 0 ∧
    quotient15At7.eval (-(7 / 65536 : ℝ)) < 0 := by
  have hp : ∀ j ≥ 4, 0 ≤ quotient14At7.coeff j ∧ quotient14At7.coeff j ≤ ((j : ℝ) + 1) ^ 14 := by
    intro j hj
    rw [quotient14At7, coeff_rowFromCoeffs]
    split
    · rename_i h
      interval_cases j <;> norm_num [quotient14Coeff]
    · exact ⟨le_rfl, by positivity⟩
  have hpa : PrefixMargin quotient14At7 14 4 (6 / 65536) 1 := by
    refine ⟨7 / 65536, by norm_num, by norm_num, ?_, ?_⟩ <;>
      norm_num [tailRatio, tailBound, prefixEval, Finset.sum_range_succ,
        quotient14At7, coeff_rowFromCoeffs, quotient14Coeff]
  have hpb : PrefixMargin quotient14At7 14 4 (7 / 65536) (-1) := by
    refine ⟨7 / 65536, by norm_num, le_rfl, ?_, ?_⟩ <;>
      norm_num [tailRatio, tailBound, prefixEval, Finset.sum_range_succ,
        quotient14At7, coeff_rowFromCoeffs, quotient14Coeff]
  have hqa : PrefixMargin quotient15At7 15 4 (6 / 65536) (-1) := by
    refine ⟨7 / 65536, by norm_num, by norm_num, ?_, ?_⟩ <;>
      norm_num [tailRatio, tailBound, prefixEval, Finset.sum_range_succ,
        quotient15At7, coeff_rowFromCoeffs, quotient15Coeff]
  have hqb : PrefixMargin quotient15At7 15 4 (7 / 65536) (-1) := by
    refine ⟨7 / 65536, by norm_num, le_rfl, ?_, ?_⟩ <;>
      norm_num [tailRatio, tailBound, prefixEval, Finset.sum_range_succ,
        quotient15At7, coeff_rowFromCoeffs, quotient15Coeff]
  refine ⟨old_product_neg_of_margins hpa hpb hp (by norm_num), ?_, ?_⟩
  · have hh := hqa.signed_pos quotient15At7_tail (by norm_num)
    linarith
  · have hh := hqb.signed_pos quotient15At7_tail (by norm_num)
    linarith

/-- The next-row sign, checked on the whole first window of the example. -/
theorem cutoff7_next_negative_on_window :
    ∀ y ∈ Set.Icc (6 / 65536 : ℝ) (7 / 65536 : ℝ), quotient15At7.eval (-y) < 0 := by
  intro y hy
  have h := signed_pos_on_window_of_horner quotient15At7 15 4
    (a := 6/65536) (b := 7/65536) (B := 7/65536) (σ := -1)
    (by norm_num) le_rfl (by norm_num [tailRatio]) quotient15At7_tail (by norm_num)
    (by norm_num [intervalHorner, tailBound, tailRatio, quotient15At7, coeff_rowFromCoeffs,
      quotient15Coeff, min_def, max_def]) y hy
  linarith

#print axioms cutoff7_next_negative_on_window
#print axioms cutoff7_first_window_14_15
#print axioms interlace_of_prefix_and_mixed_witnesses

#print axioms abs_eval_sub_prefix_le_tail
#print axioms signed_eval_pos_of_prefix_margin

end

end OpenMathResearch.LongCycleExcedances
