import OccupiedSupportNet

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter Finset
open scoped Topology PowerSeries

variable {ι : Type*} [DecidableEq ι]

/-- The finite set is the increasing tuple of occupied nondistinguished
indices in the integer lattice. Invalid repetitions of the mark are zero. -/
def occupiedCoeff (P : ι → ℂ⟦X⟧) (B : ι → ι → ℂ⟦X⟧) (N : ℕ)
    (i : ι × Finset ι) : ℂ :=
  if i.1 ∈ i.2 then 0 else PowerSeries.coeff (R := ℂ) N (P i.1 * ∏ q ∈ i.2, B i.1 q)

private theorem coeff_finset_primitive_bound (P : ℂ⟦X⟧) (B : ι → ℂ⟦X⟧)
    (N : ℕ) {V : ℝ} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hP : ∀ n ≤ N, ‖PowerSeries.coeff (R := ℂ) n P‖ ≤ V)
    (s : Finset ι) (hB : ∀ i ∈ s, ∀ n ≤ N, ‖PowerSeries.coeff (R := ℂ) n (B i)‖ ≤ w i) :
    ∀ n ≤ N, ‖PowerSeries.coeff (R := ℂ) n (P * ∏ q ∈ s, B q)‖ ≤
      V * ∏ q ∈ s, ((N:ℝ)+1)*w q := by
  induction s using Finset.induction_on with
  | empty => simpa using hP
  | @insert i s hi ih =>
    intro n hn
    rw [prod_insert hi, ← mul_left_comm (B i), PowerSeries.coeff_mul]
    rw [prod_insert hi]
    have hh := ih (fun j hj => hB j (mem_insert_of_mem hj))
    have hc : ∀ a ∈ (antidiagonal n), ‖PowerSeries.coeff (R := ℂ) a.1 (B i) *
        PowerSeries.coeff (R := ℂ) a.2 (P * ∏ q ∈ s, B q)‖ ≤
          w i * (V * ∏ q ∈ s, ((N:ℝ)+1)*w q) := by
      intro a ha
      have hsum := mem_antidiagonal.mp ha
      rw [norm_mul]
      exact mul_le_mul (hB i (mem_insert_self _ _) _ (by omega))
        (hh _ (by omega)) (norm_nonneg _) (hw i)
    calc
      _ ≤ ∑ a ∈ antidiagonal n, ‖PowerSeries.coeff (R := ℂ) a.1 (B i) *
          PowerSeries.coeff (R := ℂ) a.2 (P * ∏ q ∈ s, B q)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ antidiagonal n, w i*(V*∏ q ∈ s, ((N:ℝ)+1)*w q) := sum_le_sum hc
      _ ≤ _ := by
        rw [sum_const, Nat.card_antidiagonal, nsmul_eq_mul]
        have hV : 0 ≤ V := (norm_nonneg _).trans (hP 0 (Nat.zero_le N))
        have hp : 0 ≤ w i*(V*∏ q ∈ s, ((N:ℝ)+1)*w q) := by
          exact mul_nonneg (hw i) (mul_nonneg hV (prod_nonneg (fun q _ =>
            mul_nonneg (by positivity) (hw q))))
        have hnn : (n:ℝ)+1 ≤ (N:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hn
        push_cast
        exact (mul_le_mul_of_nonneg_right hnn hp).trans_eq (by ring)

theorem summable_occupiedCoeff (P : ι → ℂ⟦X⟧) (B : ι → ι → ℂ⟦X⟧)
    (N : ℕ) {u w : ι → ℝ} (hu : Summable u) (hw : Summable w)
    (hu0 : ∀ i, 0 ≤ u i) (hw0 : ∀ i, 0 ≤ w i)
    (hP : ∀ a n, n ≤ N → ‖PowerSeries.coeff (R := ℂ) n (P a)‖ ≤ u a)
    (hB : ∀ a q, q ≠ a → ∀ n ≤ N, ‖PowerSeries.coeff (R := ℂ) n (B a q)‖ ≤ w q) :
    Summable (fun i => ‖occupiedCoeff P B N i‖) := by
  have hw' := summable_occupied_finset (hw.mul_left ((N:ℝ)+1))
    (fun q => mul_nonneg (by positivity) (hw0 q))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hu.mul_of_nonneg hw' hu0 (fun _ => prod_nonneg (fun q _ => mul_nonneg (by positivity) (hw0 q))))
  rintro ⟨a,s⟩
  by_cases ha : a ∈ s
  · simp only [occupiedCoeff, if_pos ha, norm_zero]
    exact mul_nonneg (hu0 a) (prod_nonneg (fun q _ => mul_nonneg (by positivity) (hw0 q)))
  · simp only [occupiedCoeff, if_neg ha]
    exact coeff_finset_primitive_bound (P a) (B a) N hw0 (hP a) s
      (fun q hq => hB a q (fun h => ha (h ▸ hq))) N le_rfl

#print axioms summable_occupiedCoeff
end OpenMathResearch.LongCycleExcedances
