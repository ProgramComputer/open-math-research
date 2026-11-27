import InsertionTable
import RoundedHorner
import IntegerTail
import RepositoryActualRationalPoint
import LongCycleBounds.UniversalRecurrence

namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite LongCycleBounds.Band Polynomial Finset
open OpenMathResearch.LongCycleExcedances
open InsertionTable IntegerSign

/-- At size zero there is one permutation, with no elements and no excedances. -/
theorem enumerator_empty (k : ℕ) : enumerator 0 k = 1 := by
  classical
  simp [enumerator, Allowed, excedances]

theorem insertionEulerian_agrees (w k : ℕ) :
    agrees w (descentCoeffs (k-1)) (eulerian (k-1)) := by
  intro i _
  rw [← ofCoeffs_descentCoeffs, coeff_ofCoeffs] <;> rfl

/-- Every integer in the truncated table counts the original labelled permutations
with its indicated number of excedances. Dropped high coefficients cannot affect it. -/
theorem original_insertion_table (w n k : ℕ) (hk : 2 ≤ k) :
    agrees w ((history k (start w) (next w k (descentCoeffs (k-1))) n).getD 0 (start w))
      (enumerator n k) :=
  table_agrees w k hk _ _ (fun m => enumerator m k) (insertionEulerian_agrees w k)
    (enumerator_empty k) (fun _ => LongCycleBounds.Insertion.enumerator_succ hk) n

/-- The initial zero coefficient is discarded exactly once when passing from
the permutation enumerator to the row whose signs are measured. -/
def reducedPrefix (row : List ℤ) (W : ℕ) : List ℤ :=
  firstCoeffs (fun j => entry row (j+1)) W

theorem original_signed_point_of_rounded_prefix (n k W : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (row : List ℤ) (hr : agrees (W+1) row (enumerator n k)) (p : ℤ) (D : ℕ)
    (σ : ℚ) (hy : 0 ≤ (p : ℚ) / D) (hu : (p : ℚ) / D ≤ 1/2) (hσ : |σ|=1)
    (hq : rationalTailRatio n W ((p : ℚ)/D) < 1)
    (hm : rationalTailBound n W ((p : ℚ)/D) <
      σ * (roundedRatio p D (reducedPrefix row W) : ℚ) - 2) :
    0 < (σ : ℝ) * ((enumerator n k).divX).eval (-(((p : ℚ)/D : ℚ) : ℝ)) := by
  apply original_signed_point_of_rational_margin n k W hn hk hy hσ hq
  have h := signed_lower hy hu hσ (reducedPrefix row W)
  rw [← roundedRatio_eq p D] at h
  refine (hm.trans_le h).trans_eq ?_
  congr 1
  unfold reducedPrefix rationalPrefixEval
  rw [horner_first]
  apply sum_congr rfl
  intro j hj
  have he := hr (j+1) (by have := mem_range.mp hj; omega)
  have he' := exact_coeff_eq_original n k j hn hk
  have heq : (entry row (j+1) : ℝ) = ↑(cycleQuotientCoeff exactEulerianCoeff n k j) :=
    he.trans he'.symm
  have heq' : (entry row (j+1) : ℚ) = cycleQuotientCoeff exactEulerianCoeff n k j := by
    exact_mod_cast heq
  rw [heq']

/-- Boolean endpoint test. All divisions inside roundedRatio are Euclidean
integer divisions, including when the partial Horner accumulator is negative. -/
def integerEndpointCheck (n W : ℕ) (row : List ℤ) (p : ℤ) (D : ℕ) (s : ℤ) : Bool :=
  let U := ((W : ℤ) + 1)^n
  let V := ((W : ℤ) + 2)^n
  let Z := (D : ℤ)*U - p*V
  let M := s * roundedRatio p D (reducedPrefix row W) - 2
  decide (0 < D ∧ 0 ≤ p ∧ 2*p ≤ (D : ℤ) ∧ (s = 1 ∨ s = -1) ∧
    0 < Z ∧ (D : ℤ)*U^2*p^W < M*(D : ℤ)^W*Z)

theorem original_signed_of_integer_check (n k W : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (row : List ℤ) (hr : agrees (W+1) row (enumerator n k))
    (p : ℤ) (D : ℕ) (s : ℤ) (ok : integerEndpointCheck n W row p D s = true) :
    0 < (s : ℝ) * ((enumerator n k).divX).eval (-(((p : ℚ)/D : ℚ) : ℝ)) := by
  unfold integerEndpointCheck at ok
  obtain ⟨hD, hp, hpD, hs, hZ, hM⟩ := of_decide_eq_true ok
  obtain ⟨hq, hm⟩ := integer_tail_margin n W D p _ hD hZ hM
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hy : 0 ≤ (p : ℚ) / D := div_nonneg (by exact_mod_cast hp) hd.le
  have hu : (p : ℚ) / D ≤ 1/2 := by
    apply (div_le_iff₀ hd).mpr
    have h : 2*(p : ℚ) ≤ D := by exact_mod_cast hpD
    linarith
  have hσ : |(s : ℚ)| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have h := original_signed_point_of_rounded_prefix n k W hn hk row hr p D (s : ℚ) hy hu hσ hq
    (by exact_mod_cast hm)
  simpa using h

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.enumerator_empty
#print axioms RepositoryQuotientAudit.insertionEulerian_agrees
#print axioms RepositoryQuotientAudit.original_insertion_table
#print axioms RepositoryQuotientAudit.original_signed_point_of_rounded_prefix

#print axioms RepositoryQuotientAudit.original_signed_of_integer_check
