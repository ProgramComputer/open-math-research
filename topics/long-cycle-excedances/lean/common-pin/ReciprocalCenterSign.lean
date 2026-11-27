import StrictRootListTranslation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

namespace OpenMathResearch.LongCycleExcedances
open Polynomial

private theorem reciprocal_factor_list {d : ℕ} {P : ℝ[X]} {r : Fin d → ℝ}
    (hf : P = ∏ i, (X - C (r i))) (hm : StrictMono r) (hn : ∀ i, r i < 0)
    (hr : ∀ t : ℝ, t ≠ 0 → t^d * P.eval t⁻¹ = P.eval t) :
    (fun i : Fin d => (r i.rev)⁻¹) = r := by
  classical
  have hroot (x : ℝ) : P.eval x = 0 ↔ ∃ i, x = r i := by
    rw [hf]
    simp [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  have hinv (i : Fin d) : ∃ j, (r i)⁻¹ = r j := by
    have he := hr (r i) (hn i).ne
    rw [(hroot _).2 ⟨i, rfl⟩] at he
    exact (hroot _).1 ((mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (hn i).ne))
  have hmono : StrictMono (fun i : Fin d => (r i.rev)⁻¹) := by
    intro i j hij
    exact (inv_lt_inv_of_neg (hn i.rev) (hn j.rev)).2 (hm (Fin.rev_lt_rev.mpr hij))
  apply (hmono.range_inj hm).mp
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hinv i.rev
    exact ⟨j, hj.symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hinv i
    refine ⟨j.rev, ?_⟩
    simp [← hj]

/-- Every reciprocal pair of distinct negative roots contributes a negative
factor at minus one. The signed product of the pairs is strictly positive. -/
theorem reciprocal_even_center_sign {m : ℕ} {P : ℝ[X]} {r : Fin (m + m) → ℝ}
    (hf : P = ∏ i, (X - C (r i))) (hm : StrictMono r) (hn : ∀ i, r i < 0)
    (hr : ∀ t : ℝ, t ≠ 0 → t^(m+m) * P.eval t⁻¹ = P.eval t) :
    0 < (-1 : ℝ)^m * P.eval (-1) := by
  classical
  have hrec := reciprocal_factor_list hf hm hn hr
  have hrev (i : Fin m) : (i.castAdd m).rev = i.rev.natAdd m := by
    apply Fin.ext
    change m + m - (i.val + 1) = m + (m - (i.val + 1))
    have := i.isLt
    omega
  have hpair (i : Fin m) : r (i.rev.natAdd m) = (r (i.castAdd m))⁻¹ := by
    have h := congrFun hrec (i.castAdd m).rev
    change (r (i.castAdd m).rev.rev)⁻¹ = r (i.castAdd m).rev at h
    rw [Fin.rev_rev, hrev] at h
    exact h.symm
  have hpositive (i : Fin m) :
      0 < (-1 : ℝ) * ((-1 - r (i.castAdd m)) * (-1 - r (i.rev.natAdd m))) := by
    let a := r (i.castAdd m)
    have ha : a < 0 := hn _
    have hlt : (i.castAdd m : Fin (m + m)) < i.rev.natAdd m := by
      change i.val < m + i.rev.val
      have := i.isLt
      omega
    have hneq := (hm hlt).ne
    rw [hpair] at hneq
    change a ≠ a⁻¹ at hneq
    have hplus : a + 1 ≠ 0 := by
      intro hab
      have hneg : a = -1 := by linarith
      apply hneq
      rw [hneg]
      norm_num
    have hx : (-1-a)*(-1-a⁻¹) = (a+1)^2/a := by
      field_simp [ha.ne]
      ring
    rw [hpair]
    change 0 < (-1 : ℝ) * ((-1-a)*(-1-a⁻¹))
    rw [hx, neg_one_mul]
    exact neg_pos.mpr (div_neg_of_pos_of_neg (sq_pos_of_ne_zero hplus) ha)
  rw [hf, eval_prod, Fin.prod_univ_add]
  simp only [eval_sub, eval_X, eval_C]
  have hright :
      (∏ i : Fin m, (-1 - r (i.natAdd m))) =
      (∏ i : Fin m, (-1 - r (i.rev.natAdd m))) :=
    (Fin.rev_bijective.prod_comp (fun i : Fin m => -1 - r (i.natAdd m))).symm
  rw [hright, ← Finset.prod_mul_distrib]
  have hnegprod : (∏ _ : Fin m, (-1 : ℝ)) = (-1 : ℝ)^m := by simp
  rw [← hnegprod, ← Finset.prod_mul_distrib]
  exact Finset.prod_pos (fun i _ => hpositive i)

#print axioms reciprocal_even_center_sign
end OpenMathResearch.LongCycleExcedances
