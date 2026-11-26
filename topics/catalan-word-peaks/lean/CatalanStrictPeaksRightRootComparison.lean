import CatalanStrictPeaksInterlacing
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rightmost-root comparison from the logarithmic derivative

Once the pole estimates give the value and logarithmic derivative at the
coalescence parameter, the checked gap to the other roots isolates the
closest reciprocal term.
-/

open Finset OpenMathResearch.OrientedNegativeInterlace
open scoped BigOperators

namespace CatalanStrictPeaks.RightEdge

private theorem factorization {m : ℕ} {P : Polynomial ℝ} {r : Fin m → ℝ}
    (hr : CompleteNegativeRoots P r) :
    P = Polynomial.C P.leadingCoeff * ∏ i, (Polynomial.X - Polynomial.C (-r i)) := by
  classical
  have hinj : Function.Injective (fun i => -r i) := neg_injective.comp hr.2.1.injective
  have hc : P.roots.card = P.natDegree := by
    rw [hr.2.2.2, hr.1]
    change (Finset.univ.image (fun i => -r i)).card = m
    simpa using Finset.card_image_of_injective (s := Finset.univ) hinj
  have h := (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hc).symm
  rw [hr.2.2.2] at h
  refine h.trans (congrArg (fun q => Polynomial.C P.leadingCoeff * q) ?_)
  change (∏ x ∈ Finset.univ.image (fun i => -r i), (Polynomial.X - Polynomial.C x)) = _
  exact Finset.prod_image (fun _ _ _ _ h => hinj h)

private theorem eval_factorization {m : ℕ} {P : Polynomial ℝ} {r : Fin m → ℝ}
    (hr : CompleteNegativeRoots P r) (t : ℝ) :
    P.eval t = P.leadingCoeff * ∏ i, (t + r i) := by
  rw [factorization hr, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
  rw [← factorization hr]

private theorem derivative_product {ι : Type*} [DecidableEq ι] (r : ι → ℝ) (t : ℝ)
    (s : Finset ι) (ht : ∀ i ∈ s, t + r i ≠ 0) :
    (Polynomial.derivative (∏ i ∈ s, (Polynomial.X - Polynomial.C (-r i)))).eval t =
      (∏ i ∈ s, (t + r i)) * ∑ i ∈ s, (t + r i)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hti := ht i (Finset.mem_insert_self _ _)
    have hts : ∀ j ∈ s, t + r j ≠ 0 := fun j hj => ht j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi,
      Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
      Polynomial.eval_one, one_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_neg_eq_add, Polynomial.eval_prod, ih hts]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    field_simp [hti]
    ring

private theorem logDerivative_roots {m : ℕ} {P : Polynomial ℝ} {r : Fin m → ℝ} (t : ℝ)
    (hr : CompleteNegativeRoots P r) (ht : ∀ i, 0 < t + r i)
    (hvalue : 0 < P.eval t) :
    P.derivative.eval t / P.eval t = ∑ i, (t + r i)⁻¹ := by
  classical
  have hderiv : P.derivative.eval t = P.leadingCoeff *
      ((∏ i, (t + r i)) * ∑ i, (t + r i)⁻¹) := by
    conv_lhs => rw [factorization hr, Polynomial.derivative_mul, Polynomial.derivative_C,
      zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [derivative_product r t Finset.univ (fun i _ => (ht i).ne')]
  apply (div_eq_iff hvalue.ne').mpr
  rw [hderiv, eval_factorization hr]
  ring

private def firstIndex (n : ℕ) (hn : 150 ≤ n) : Fin (rowDegree n) :=
  ⟨0, by unfold rowDegree; omega⟩

private theorem ne_first_pos {n : ℕ} (hn : 150 ≤ n) {i : Fin (rowDegree n)}
    (hi : i ≠ firstIndex n hn) : 0 < i.val := by
  by_contra! h
  exact hi (Fin.ext (by dsimp [firstIndex]; omega))

private theorem first_gap_pos {n : ℕ} (hn : 150 ≤ n) {r : Fin (rowDegree n) → ℝ}
    (hr : CompleteNegativeRoots (C n) r) (hvalue : 0 < (C n).eval (-11 / 16))
    (htail : ∀ i : Fin (rowDegree n), 0 < i.val → 11 / 16 + 1 / (n : ℝ) ^ 2 < r i) :
    ∀ i, 0 < (-11 / 16 : ℝ) + r i := by
  classical
  let i₀ := firstIndex n hn
  have htailPos : ∀ i, i ≠ i₀ → 0 < (-11 / 16 : ℝ) + r i := by
    intro i hi
    have h := htail i (ne_first_pos hn hi)
    linarith [show 0 ≤ 1 / (n : ℝ) ^ 2 by positivity]
  intro i
  by_cases hi : i = i₀
  · subst i
    rw [eval_factorization hr, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)] at hvalue
    have hprod : 0 < ∏ i ∈ Finset.univ.erase i₀, ((-11 / 16 : ℝ) + r i) := by
      exact Finset.prod_pos (fun j hj => htailPos j (Finset.ne_of_mem_erase hj))
    apply (mul_pos_iff_of_pos_right hprod).mp
    exact (mul_pos_iff_of_pos_left (leadingCoeff_pos n)).mp hvalue
  · exact htailPos i hi

private theorem inverse_tail_bounds {n : ℕ} (hn : 150 ≤ n) {r : Fin (rowDegree n) → ℝ}
    (htail : ∀ i : Fin (rowDegree n), 0 < i.val → 11 / 16 + 1 / (n : ℝ) ^ 2 < r i) :
    let t := ∑ i ∈ Finset.univ.erase (firstIndex n hn), ((-11 / 16 : ℝ) + r i)⁻¹
    0 ≤ t ∧ t ≤ (n : ℝ) ^ 3 := by
  classical
  dsimp only
  let s := Finset.univ.erase (firstIndex n hn)
  have hpos (i : Fin (rowDegree n)) (hi : i ∈ s) : 0 < (-11 / 16 : ℝ) + r i := by
    have h := htail i (ne_first_pos hn (Finset.ne_of_mem_erase hi))
    linarith [show 0 ≤ 1 / (n : ℝ) ^ 2 by positivity]
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact Finset.sum_nonneg (fun i hi => (inv_pos.mpr (hpos i hi)).le)
  · calc
      _ ≤ ∑ _ ∈ s, (n : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := htail i (ne_first_pos hn (Finset.ne_of_mem_erase hi))
        have hp : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        have hle : ((n : ℝ) ^ 2)⁻¹ ≤ (-11 / 16 : ℝ) + r i := by
          rw [← one_div]
          linarith
        simpa only [inv_inv] using (inv_le_inv₀ (hpos i hi) (inv_pos.mpr hp)).mpr hle
      _ = (s.card : ℝ) * (n : ℝ) ^ 2 := by simp
      _ ≤ _ := by
        have hcard : s.card ≤ n :=
          (Finset.card_le_univ _).trans (by simp [rowDegree]; omega)
        calc
          _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
          _ = _ := by ring

/-- The two logarithmic-derivative estimates at the coalescence point,
with the checkpoint separation, give the exact rightmost-root sign. -/
theorem rightmost_sign_of_logDerivative_growth {n : ℕ} (hn : 150 ≤ n)
    {old : Fin (rowDegree n) → ℝ} {new : Fin (rowDegree (n + 1)) → ℝ}
    (hOld : CompleteNegativeRoots (C n) old) (hNew : CompleteNegativeRoots (C (n + 1)) new)
    (hgap : ∀ i : Fin (rowDegree n), 0 < i.val → 11 / 16 + 1 / (n : ℝ) ^ 2 < old i)
    (hgap' : ∀ i : Fin (rowDegree (n + 1)), 0 < i.val →
      11 / 16 + 1 / ((n + 1 : ℕ) : ℝ) ^ 2 < new i)
    (hv : 0 < (C n).eval (-11 / 16)) (hv' : 0 < (C (n + 1)).eval (-11 / 16))
    (hlog : 300 * (n : ℝ) ^ 3 < (C n).derivative.eval (-11 / 16) / (C n).eval (-11 / 16))
    (hstep : 100 * (n : ℝ) ^ 3 <
      (C (n + 1)).derivative.eval (-11 / 16) / (C (n + 1)).eval (-11 / 16) -
        (C n).derivative.eval (-11 / 16) / (C n).eval (-11 / 16))
    (i : Fin (rowDegree n)) (hi : i.val = 0) : (C (n + 1)).eval (-old i) < 0 := by
  classical
  rw [show i = firstIndex n hn from Fin.ext hi]
  have hn' : 150 ≤ n + 1 := by omega
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  let i₀ := firstIndex n hn
  let i₀' := firstIndex (n + 1) hn'
  let τ : ℝ := -11 / 16
  let A := τ + old i₀
  let B := τ + new i₀'
  let T := ∑ i ∈ Finset.univ.erase i₀, (τ + old i)⁻¹
  let U := ∑ i ∈ Finset.univ.erase i₀', (τ + new i)⁻¹
  have hA : 0 < A := first_gap_pos hn hOld hv hgap i₀
  have hB : 0 < B := first_gap_pos hn' hNew hv' hgap' i₀'
  have hl := logDerivative_roots τ hOld (first_gap_pos hn hOld hv hgap) hv
  have hr := logDerivative_roots τ hNew (first_gap_pos hn' hNew hv' hgap') hv'
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀')] at hr
  change _ = A⁻¹ + T at hl
  change _ = B⁻¹ + U at hr
  change 300 * (n : ℝ) ^ 3 < (C n).derivative.eval τ / (C n).eval τ at hlog
  change 100 * (n : ℝ) ^ 3 <
    (C (n + 1)).derivative.eval τ / (C (n + 1)).eval τ -
        (C n).derivative.eval τ / (C n).eval τ at hstep
  rw [hl] at hlog
  rw [hr, hl] at hstep
  obtain ⟨hT₀, hT⟩ := inverse_tail_bounds hn hgap
  obtain ⟨_, hU⟩ := inverse_tail_bounds hn' hgap'
  change 0 ≤ T at hT₀
  change T ≤ (n : ℝ) ^ 3 at hT
  change U ≤ ((n + 1 : ℕ) : ℝ) ^ 3 at hU
  push_cast at hU
  have hs : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hc3 : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hs 3
      _ = _ := by ring
  have hBinv : A⁻¹ < B⁻¹ := by linarith [hc3, show 0 ≤ (n : ℝ) ^ 3 by positivity]
  have hBA : B < A := (inv_lt_inv₀ hA hB).mp hBinv
  have hAn : ((n : ℝ) + 1) ^ 2 < A⁻¹ := by
    have hs' : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      calc
        _ ≤ (2 * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
        _ = _ := by ring
    nlinarith only [hlog, hT, hs', mul_nonneg (sq_nonneg (n : ℝ))
      (show 0 ≤ (n : ℝ) - 1 by linarith)]
  have hAinv : A < 1 / ((n : ℝ) + 1) ^ 2 := by
    have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    rw [one_div]
    apply (inv_lt_inv₀ (inv_pos.mpr hp) hA).mp
    simpa only [one_div, inv_inv] using hAn
  have htail : 0 < ∏ i ∈ Finset.univ.erase i₀', (-old i₀ + new i) := by
    apply Finset.prod_pos
    intro i hi
    have hh := hgap' i (ne_first_pos hn' (Finset.ne_of_mem_erase hi))
    push_cast at hh
    dsimp [A, τ] at hAinv
    linarith only [hh, hAinv]
  rw [eval_factorization hNew, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀')]
  exact mul_neg_of_pos_of_neg (leadingCoeff_pos (n + 1))
    (mul_neg_of_neg_of_pos (show -old i₀ + new i₀' < 0 by dsimp [B, A, τ] at hBA; linarith) htail)

end CatalanStrictPeaks.RightEdge
