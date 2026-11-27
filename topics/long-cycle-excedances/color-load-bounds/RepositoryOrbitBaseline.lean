import MarkedColorLoads
import RepositoryProbabilityBands
import LongCycleBounds.UniversalInsertion

set_option autoImplicit false
noncomputable section

namespace OpenMathResearch.LongCycleExcedances.CycleProbability

/-- The first block of positive masses is exactly reciprocal in the size.
The adjacent recurrence preserves the interval with those endpoint values. -/
theorem Spec.reciprocal_bounds {b p : ℕ} {d : ℕ → ℝ} (h : Spec b d)
    (hb : 0 < b) (hp : b ≤ p) :
    1/(2*(b:ℝ)-1) ≤ d p ∧ d p ≤ 1/(b:ℝ) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    have hp' : (0:ℝ) < p := by exact_mod_cast hb.trans_le hp
    by_cases hbase : p < 2*b
    · rw [one_cycle h hp hbase]
      have hlo' : (p:ℝ) ≤ 2*(b:ℝ)-1 := by
        have hn : p+1 ≤ 2*b := by omega
        have hcast : (p:ℝ)+1 ≤ 2*(b:ℝ) := by exact_mod_cast hn
        linarith only [hcast]
      exact ⟨div_le_div_of_nonneg_left (by norm_num) hp' hlo',
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast hp)⟩
    · have prev := ih (p-1) (by omega) (by omega)
      have lag := ih (p-b) (by omega) (by omega)
      have hrec := adjacent h (show b < p by omega)
      have hcast : (p:ℝ) = ((p-1:ℕ):ℝ)+1 := by
        exact_mod_cast (show p=(p-1)+1 by omega)
      have hprev : (0:ℝ) ≤ ((p-1:ℕ):ℝ) := by positivity
      have hl := add_le_add (mul_le_mul_of_nonneg_left prev.1 hprev) lag.1
      have hu := add_le_add (mul_le_mul_of_nonneg_left prev.2 hprev) lag.2
      rw [←hrec] at hl hu
      have scale (c : ℝ) : ((p-1:ℕ):ℝ)*c+c = (p:ℝ)*c := by
        rw [hcast,add_mul,one_mul]
      rw [scale] at hl hu
      constructor
      · by_contra! hh
        exact (not_lt_of_ge hl) (mul_lt_mul_of_pos_left hh hp')
      · by_contra! hh
        exact (not_lt_of_ge hu) (mul_lt_mul_of_pos_left hh hp')

end OpenMathResearch.LongCycleExcedances.CycleProbability

namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Equiv Function LongCycles LongCycleBounds.Insertion
open OpenMathResearch.LongCycleExcedances.CycleProbability

/-- The same-cycle subtype includes its starting point, also for a fixed point. -/
theorem orbitSize_eq_lengthAt {p : ℕ} (π : Perm (Fin p)) (c : Fin p) :
    orbitSize π c = lengthAt π c := by
  let index (i : Fin (lengthAt π c)) : {x : Fin p // π.SameCycle c x} :=
    ⟨(π ^ i.val) c, Perm.SameCycle.rfl.pow_right⟩
  have hinj : Injective index := by
    intro i j hij
    have he := congrArg Subtype.val hij
    change (π ^ i.val) c = (π ^ j.val) c at he
    rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow] at he
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).1 he)
  have hsurj : Surjective index := by
    intro x
    obtain ⟨q,hq⟩ := x.property.exists_nat_pow_eq
    have hpos := lengthAt_pos π c
    refine ⟨⟨q % lengthAt π c, Nat.mod_lt _ hpos⟩, Subtype.ext ?_⟩
    change (π ^ (q % lengthAt π c)) c = x.val
    calc
      _ = (π ^ q) c := by
        rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow]
        exact iterate_mod_minimalPeriod_eq
      _ = _ := hq
  unfold orbitSize
  rw [← Nat.card_congr (Equiv.ofBijective index ⟨hinj, hsurj⟩),
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem enumerator_eval_one_eq_card (p b : ℕ) :
    (enumerator p b).eval 1 = (Nat.card {π : Perm (Fin p) // Allowed b π}:ℝ) := by
  classical
  unfold enumerator
  change (Polynomial.evalRingHom (1:ℝ)) _ = _
  rw [map_sum, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Polynomial.coe_evalRingHom, apply_ite (Polynomial.eval (1:ℝ)),
    Polynomial.eval_pow, Polynomial.eval_X, one_pow, Polynomial.eval_zero]
  rw [← Finset.sum_filter]
  simp

/-- The free word contributes exactly p^n independent choices. -/
theorem baselinePairs_card (n p b : ℕ) :
    Nat.card (BaselinePairs n p b) =
      p^n * Nat.card {π : Perm (Fin p) // Allowed b π} := by
  have hp (π : Perm (Fin p)) : (∀ c, b ≤ orbitSize π c) ↔ Allowed b π := by
    simp only [orbitSize_eq_lengthAt, allowed_iff_lengthAt]
  let e : BaselinePairs n p b ≃ (Fin n → Fin p) × {π : Perm (Fin p) // Allowed b π} :=
    { toFun := fun w => (w.val.1, ⟨w.val.2, (hp _).mp w.property⟩)
      invFun := fun w => ⟨(w.1,w.2.val), (hp _).mpr w.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Normalizing the entire product space gives the repository's original
permutation probability. The cutoff may be one. -/
theorem baselinePairs_probability {n p b : ℕ} (hp : 0 < p) :
    (Nat.card (BaselinePairs n p b):ℝ)/((p.factorial:ℝ)*(p:ℝ)^n) =
      originalProbability b p := by
  have hpn : (p:ℝ)^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  rw [baselinePairs_card, Nat.cast_mul, Nat.cast_pow, originalProbability,
    enumerator_eval_one_eq_card]
  rw [mul_comm ((p:ℝ)^n), mul_div_mul_right _ _ hpn]

theorem originalProbability_one (p : ℕ) : originalProbability 1 p = 1 := by
  have hp (π : Perm (Fin p)) : Allowed 1 π := by
    intro x j hj hsmall
    omega
  classical
  have h : Nat.card {π : Perm (Fin p) // Allowed 1 π} = p.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [hp, Fintype.card_perm]
  rw [originalProbability, enumerator_eval_one_eq_card, h, div_self (by positivity)]

theorem originalProbability_reciprocal_bounds {p b : ℕ} (hb : 0 < b) (hp : b ≤ p) :
    1/(2*(b:ℝ)-1) ≤ originalProbability b p ∧
      originalProbability b p ≤ 1/(b:ℝ) := by
  rcases eq_or_ne b 1 with he | he
  · subst b
    norm_num [originalProbability_one]
  · exact (originalProbability_spec (by omega : 2 ≤ b)).reciprocal_bounds hb hp

theorem baselinePairs_probability_bounds {n p b : ℕ} (hb : 0 < b) (hp : b ≤ p) :
    let d := (Nat.card (BaselinePairs n p b):ℝ)/((p.factorial:ℝ)*(p:ℝ)^n)
    1/(2*(b:ℝ)-1) ≤ d ∧ d ≤ 1/(b:ℝ) := by
  dsimp only
  rw [baselinePairs_probability (hb.trans_le hp)]
  exact originalProbability_reciprocal_bounds hb hp

#print axioms CycleProbability.Spec.reciprocal_bounds
#print axioms orbitSize_eq_lengthAt
#print axioms baselinePairs_card
#print axioms baselinePairs_probability
#print axioms originalProbability_one
#print axioms originalProbability_reciprocal_bounds
#print axioms baselinePairs_probability_bounds
end OpenMathResearch.LongCycleExcedances.ColorAnchor
