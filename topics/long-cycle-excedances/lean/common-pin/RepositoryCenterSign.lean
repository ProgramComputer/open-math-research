import RepositoryHalfAxisAssembly
import ReciprocalCenterSign
import LongCycleBounds.AnchoredRows

namespace RepositoryQuotientAudit
open Polynomial Finset LongCycles LongCycleBounds LongCycleBounds.Band
open OpenMathResearch.LongCycleExcedances

private theorem odd_cycle_center_zero {a : ℕ} (ha : 2 ≤ a) (ho : Odd a) :
    (eulerian (a - 1)).eval (-1) = 0 := by
  have hd : Odd (a - 2) := by
    obtain ⟨w, hw⟩ := ho
    exact ⟨w - 1, by omega⟩
  have hz := reciprocal_center_root_of_odd
    (fun t ht => eulerian_reciprocity (a - 2) (t := t) ht) hd
  have he : a - 2 + 1 = a - 1 := by omega
  simpa only [he, IsRoot] using hz

private theorem even_cycle_center_pos {a : ℕ} (ha : 2 ≤ a) (he : Even a) :
    0 < (-1 : ℝ)^(a / 2) * (-1 * (eulerian (a - 1)).eval (-1)) := by
  let m := a / 2 - 1
  obtain ⟨w, hw⟩ := he
  have hindex : m + m + 1 = a - 1 := by dsimp [m]; omega
  have hpow : a / 2 = m + 1 := by dsimp [m]; omega
  obtain ⟨r, hf, hm, hn⟩ := eulerian_simple_negative (m + m)
  have hpos := reciprocal_even_center_sign hf hm hn
    (fun t ht => eulerian_reciprocity (m + m) (t := t) ht)
  rw [hindex] at hpos
  rw [hpow, pow_succ]
  convert hpos using 1
  ring

private theorem enumerator_empty_row (k : ℕ) (hk : 2 ≤ k) :
    enumerator 0 k = 1 := by
  rw [CycleCount.enumerator_ordered_cycle_rows hk]
  simp [CycleCount.orderedCycleRow]

/-- All even original rows have nonnegative signed center value. When
the cutoff fits, the single full-size cycle makes the sign strict. -/
theorem original_even_center (k m : ℕ) (hk : 2 ≤ k) :
    0 ≤ (-1 : ℝ)^m * (enumerator (m + m) k).eval (-1) ∧
      (k ≤ m + m → 0 < (-1 : ℝ)^m * (enumerator (m + m) k).eval (-1)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      simp [enumerator_empty_row k hk]
    have hN : 0 < m + m := by omega
    let term (a : ℕ) : ℝ :=
      (-1 : ℝ)^m * ((((m + m - 1).choose (a - 1)) : ℝ) *
        (-1 * (eulerian (a - 1)).eval (-1)) * (enumerator (m + m - a) k).eval (-1))
    have hsum :
        (-1 : ℝ)^m * (enumerator (m + m) k).eval (-1) =
          ∑ a ∈ Icc k (m + m), term a := by
      rw [LongCycleBounds.Anchored.anchored_row_recurrence hk (⟨0, hN⟩ : Fin (m + m)),
        eval_finsetSum, mul_sum]
      simp only [term, eval_mul, eval_C, eval_X]
    have hterm (a : ℕ) (hmem : a ∈ Icc k (m + m)) : 0 ≤ term a := by
      obtain ⟨hka, haN⟩ := mem_Icc.mp hmem
      rcases Nat.even_or_odd a with he | ho
      · have hcycle := even_cycle_center_pos (hk.trans hka) he
        obtain ⟨b, hb⟩ := he
        have hbpos : 0 < b := by omega
        have hbm : b ≤ m := by omega
        have hsmall : m - b < m := by omega
        have ha2 : a / 2 = b := by omega
        rw [ha2] at hcycle
        have hrem : m + m - a = (m - b) + (m - b) := by omega
        have hp : (-1 : ℝ)^m = (-1)^b * (-1)^(m-b) := by
          rw [← pow_add, Nat.add_sub_of_le hbm]
        have hres := (ih (m - b) hsmall).1
        have hweight : 0 ≤ (((m + m - 1).choose (a - 1)) : ℝ) := by positivity
        have heq : term a = (((m + m - 1).choose (a - 1)) : ℝ) *
            ((-1)^b * (-1 * (eulerian (a - 1)).eval (-1))) *
            ((-1)^(m-b) * (enumerator ((m-b) + (m-b)) k).eval (-1)) := by
          dsimp [term]
          rw [hp, hrem]
          ring
        rw [heq]
        exact mul_nonneg (mul_nonneg hweight hcycle.le) hres
      · simp [term, odd_cycle_center_zero (hk.trans hka) ho]
    rw [hsum]
    refine ⟨sum_nonneg hterm, ?_⟩
    intro hkn
    have hsingle : 0 < term (m+m) := by
      have hE := even_cycle_center_pos (hk.trans hkn) (show Even (m+m) from ⟨m, rfl⟩)
      have hhalf : (m + m) / 2 = m := by omega
      rw [hhalf] at hE
      simpa only [term, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        enumerator_empty_row k hk, eval_one, mul_one] using hE
    exact sum_pos' hterm ⟨m+m, mem_Icc.mpr ⟨hkn, le_rfl⟩, hsingle⟩

/-- The center sign needed by the actual odd-old-degree half-axis theorem.
It follows from the anchored expansion and the strict single-cycle term. -/
theorem original_next_center_sign {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (ho : Odd (n-2)) :
    0 < (-1 : ℝ)^((n-2)/2+1) * (enumerator (n+1) k).divX.eval (-1) := by
  let m := (n+1)/2
  obtain ⟨w, hw⟩ := ho
  have hnm : n+1 = m+m := by dsimp [m]; omega
  have hpower : (n-2)/2+1+1 = m := by dsimp [m]; omega
  have hpos := (original_even_center k m hk).2 (by omega)
  rw [← hnm] at hpos
  have hfactor : enumerator (n+1) k = X * (enumerator (n+1) k).divX :=
    (actual_general_cycle_row hk (by omega : 0 < n+1)).trans
      (congrArg (fun P : ℝ[X] => X * P) (generalCycleQuotient_eq_divX (n+1) k (by omega) hk))
  have heval := congrArg (fun P : ℝ[X] => P.eval (-1)) hfactor
  simp only [eval_mul, eval_X] at heval
  rw [← hpower, pow_succ, heval] at hpos
  convert hpos using 1
  ring

/-- A complete family of left-half witnesses now suffices at every
admissible size. The original center sign is supplied by the exact sum. -/
theorem original_weak_of_left_windows {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    let P := (enumerator n k).divX
    let Q := (enumerator (n + 1) k).divX
    ∀ (l u : Fin ((n - 2) / 2) → ℝ)
    (_hpos : ∀ i, 0 < l i) (_hbelow : ∀ i, u i < 1)
    (_horder : ∀ i j, i < j → u i < l j)
    (_hold : ∀ i, (l i = u i ∧ P.IsRoot (-l i)) ∨
      (l i < u i ∧ P.eval (-l i) * P.eval (-u i) < 0))
    (_hsLeft : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-l i))
    (_hsRight : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (-u i)),
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  dsimp only
  intro l u hpos hbelow horder hold hsLeft hsRight
  exact original_weak_of_half_axis_windows hk hn l u hpos hbelow horder hold hsLeft hsRight
    (original_next_center_sign hk hn)

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.original_even_center
#print axioms RepositoryQuotientAudit.original_next_center_sign
#print axioms RepositoryQuotientAudit.original_weak_of_left_windows
