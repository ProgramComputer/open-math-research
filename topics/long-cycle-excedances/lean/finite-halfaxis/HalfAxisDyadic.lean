import RepositoryStrictHalfWindows
import LongCycleFinite.Rounded

namespace RepositoryQuotientAudit

open Polynomial LongCycles LongCycleFinite

structure HalfAxisDyadicWindow where
  lower : Dyadic
  upper : Dyadic

private def negDyadic (a : Dyadic) : Dyadic := ⟨-a.numer, a.shift⟩

private theorem value_negDyadic (a : Dyadic) : (negDyadic a).value = -a.value := by
  simp [negDyadic, Dyadic.value, neg_div]

private def oddSign (i : ℕ) : Bool := decide (i % 2 = 1)

private theorem opposite_signs {b : Bool} {x y : ℝ}
    (hx : if b then x < 0 else 0 < x)
    (hy : if !b then y < 0 else 0 < y) : x * y < 0 := by
  cases b <;> simp at hx hy
  · exact mul_neg_of_pos_of_neg hx hy
  · exact mul_neg_of_neg_of_pos hx hy

private theorem signed_pow_pos {x : ℝ} (i : ℕ)
    (h : if oddSign i then x < 0 else 0 < x) :
    0 < (-1 : ℝ)^i * x := by
  rcases Nat.even_or_odd i with he | ho
  · have hm : i % 2 = 0 := Nat.even_iff.mp he
    simpa [oddSign, hm, he.neg_one_pow] using h
  · have hm : i % 2 = 1 := Nat.odd_iff.mp ho
    simpa [oddSign, hm, ho.neg_one_pow] using h

/-- The finite witness checker uses only integer comparisons and directed Horner
evaluation. Window endpoints are positive moduli in increasing order. -/
def halfAxisDyadicOK (n : ℕ) (p q : List ℤ)
    (windows : Fin ((n - 2) / 2) → HalfAxisDyadicWindow) : Bool :=
  (List.finRange ((n - 2) / 2)).all (fun i =>
    let w := windows i
    Dyadic.zero.less w.lower && w.lower.less w.upper &&
      w.upper.less ⟨1, 0⟩ &&
      roundedSign (oddSign i.val) p (negDyadic w.lower) &&
      roundedSign (!oddSign i.val) p (negDyadic w.upper) &&
      roundedSign (oddSign (i.val + 1)) q (negDyadic w.lower) &&
      roundedSign (oddSign (i.val + 1)) q (negDyadic w.upper) &&
      (List.finRange ((n - 2) / 2)).all (fun j =>
        if i < j then w.upper.less (windows j).lower else true)) &&
    (if (n - 2) % 2 = 1 then
      roundedSign (oddSign ((n - 2) / 2 + 1)) q ⟨-1, 0⟩ else true)

theorem original_strict_and_weak_of_checked_half_axis {n k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (p q : List ℤ) (hp : ofCoeffs p = (enumerator n k).divX)
    (hq : ofCoeffs q = (enumerator (n + 1) k).divX)
    (windows : Fin ((n - 2) / 2) → HalfAxisDyadicWindow)
    (hcheck : halfAxisDyadicOK n p q windows = true) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n + 1) k).divX (n - 2) ∧
    WeakRealInterlacing (enumerator n k) (enumerator (n + 1) k) := by
  obtain ⟨hw, hc⟩ := Bool.and_eq_true_iff.mp hcheck
  have hw' (i : Fin ((n - 2) / 2)) :=
    (List.all_eq_true.mp hw) i (by simp)
  have hdata (i : Fin ((n - 2) / 2)) := hw' i
  simp only [Bool.and_eq_true_iff] at hdata
  apply original_strict_and_weak_of_half_axis_windows hk hn
    (fun i => (windows i).lower.value) (fun i => (windows i).upper.value)
  · intro i
    simpa using (Dyadic.less_iff _ _).mp (hdata i).1.1.1.1.1.1.1
  · intro i
    simpa [Dyadic.value] using (Dyadic.less_iff _ _).mp (hdata i).1.1.1.1.1.2
  · intro i j hij
    have hh := (List.all_eq_true.mp (hdata i).2) j (by simp)
    exact (Dyadic.less_iff _ _).mp (by simpa [hij] using hh)
  · intro i
    refine Or.inr ⟨(Dyadic.less_iff _ _).mp (hdata i).1.1.1.1.1.1.2, ?_⟩
    have hl := roundedSign_sound _ _ _ (hdata i).1.1.1.1.2
    have hu := roundedSign_sound _ _ _ (hdata i).1.1.1.2
    simpa only [hp, value_negDyadic] using opposite_signs hl hu
  · intro i
    have hs := roundedSign_sound _ _ _ (hdata i).1.1.2
    simpa only [hq, value_negDyadic] using signed_pow_pos (i.val + 1) hs
  · intro i
    have hs := roundedSign_sound _ _ _ (hdata i).1.2
    simpa only [hq, value_negDyadic] using signed_pow_pos (i.val + 1) hs
  · intro ho
    have hsign : roundedSign (oddSign ((n - 2) / 2 + 1)) q ⟨-1, 0⟩ = true := by
      simpa [Nat.odd_iff.mp ho] using hc
    have hs := roundedSign_sound _ _ _ hsign
    simpa [hq, Dyadic.value] using signed_pow_pos ((n - 2) / 2 + 1) hs

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.original_strict_and_weak_of_checked_half_axis
