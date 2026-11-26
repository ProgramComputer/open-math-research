import CatalanStrictPeaks
import OpenMathResearch.OrientedNegativeInterlace
import OpenMathResearch.IntegerLevelNodes

/-!
# Root count and directed interlacing for strict Catalan peaks

The division of the analytic proof into checkpoint signs and signs at old
roots is explicit in the hypotheses. The polynomial is defined directly by
enumeration of the Catalan words.
-/

namespace CatalanStrictPeaks

open Polynomial Set
open OpenMathResearch.OrientedNegativeInterlace

/-- Consecutive Catalan peak polynomials with the rightmost new zero first.
All root moduli are listed in increasing order. -/
def StrictlyInterlaces (n : ℕ) : Prop :=
  ∃ old : Fin (rowDegree n) → ℝ, ∃ new : Fin (rowDegree (n + 1)) → ℝ,
    CompleteNegativeRoots (C n) old ∧ CompleteNegativeRoots (C (n + 1)) new ∧
      Oriented old new

/-- Checkpoint hypotheses for the phase in units of pi. Continuity and the
endpoint values select the finite test points. The positive leading
coefficient supplies the last sign independently of the phase. -/
structure Checkpoints (n : ℕ) where
  left : ℝ
  right : ℝ
  phase : ℝ → ℝ
  modulus : ℝ → ℝ
  interval : left < right
  continuous : ContinuousOn phase (Icc left right)
  leftPhase : phase left = 1 / 4
  rightPhase : phase right = (n : ℝ) / 2 - 1 / 8
  modulusOrder : StrictMonoOn modulus (Ioo left right)
  modulusPos : ∀ x ∈ Ioo left right, 0 < modulus x
  signs : ∀ k : ℕ, 0 < k → k < rowDegree n → ∀ x ∈ Ioo left right,
    phase x = (k : ℝ) → 0 < (-1 : ℝ) ^ k * (C n).eval (-modulus x)

/-- The exact degree of the strict-peak row is exhausted by simple negative
roots once the analytic checkpoint signs hold. -/
theorem roots_from_checkpoints {n : ℕ} (hn : 3 ≤ n) (H : Checkpoints n) :
    ∃ roots : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) roots := by
  let m := rowDegree n - 1
  have hd : rowDegree n = m + 1 := by
    dsimp [m, rowDegree]
    omega
  have hmNat : 2 * m + 3 ≤ n := by
    dsimp [m, rowDegree]
    omega
  have hmReal : 2 * (m : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hmNat
  have hL : H.phase H.left < 1 := by rw [H.leftPhase]; norm_num
  have hR : (m : ℝ) < H.phase H.right := by rw [H.rightPhase]; linarith
  obtain ⟨t, hmono, hmem, heval⟩ :=
    OpenMathResearch.IntegerLevelNodes.increasing_integer_level_nodes
      H.interval H.continuous hL m hR
  let q (i : Fin m) := H.modulus (t i)
  have hq : StrictMono q := fun i j hij => H.modulusOrder (hmem i) (hmem j) (hmono hij)
  have hqp (i : Fin m) : 0 < q i := H.modulusPos (t i) (hmem i)
  have hs (i : Fin m) : 0 < (-1 : ℝ) ^ (i.val + 1) * (C n).eval (-q i) :=
    H.signs (i.val + 1) (Nat.succ_pos _) (by have hi := i.isLt; omega)
      (t i) (hmem i) (heval i)
  obtain ⟨roots, hroots, _⟩ :=
    roots_of_signed_test_points (C n) q (natDegree_C n) (Or.inr hd) hq hqp
      (eval_zero_pos n) (leadingCoeff_pos n) hs
  exact ⟨roots, hroots⟩

/-- If the old roots are known and the next row has the signed values
proved by the analytic comparison, this gives the exact oriented pair.
It handles both adjacent degree patterns of the Catalan peak polynomials. -/
theorem next_from_old_root_signs {n : ℕ} {old : Fin (rowDegree n) → ℝ}
    (hOld : CompleteNegativeRoots (C n) old)
    (signs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * (C (n + 1)).eval (-old i)) :
    StrictlyInterlaces n := by
  have hd : rowDegree (n + 1) = rowDegree n ∨ rowDegree (n + 1) = rowDegree n + 1 := by
    unfold rowDegree
    omega
  obtain ⟨new, hNew, hOrientation⟩ :=
    next_of_signs_at_all_old_roots hOld (natDegree_C (n + 1)) hd
      (eval_zero_pos (n + 1)) (leadingCoeff_pos (n + 1)) signs
  exact ⟨old, new, hOld, hNew, hOrientation⟩

/-- Equal degree for odd old rows. -/
theorem odd_step_degree (m : ℕ) :
    rowDegree (2 * m + 1) = m ∧ rowDegree (2 * m + 2) = m := by
  unfold rowDegree
  omega

/-- Degree increases by one for positive even old rows. -/
theorem positive_even_step_degree (m : ℕ) :
    rowDegree (2 * m + 2) = m ∧ rowDegree (2 * m + 3) = m + 1 := by
  unfold rowDegree
  omega

/-- The exact split of the proposed argument at n = 150. The hypotheses are
the finite prefix, the uniform checkpoint signs, and the signed comparisons
at all old roots. -/
theorem interlacing_from_finite_and_analytic_signs
    (finite : ∀ n < 150, StrictlyInterlaces n)
    (checkpoints : ∀ n, 150 ≤ n → Checkpoints n)
    (oldRootSigns : ∀ n, 150 ≤ n → ∀ old : Fin (rowDegree n) → ℝ,
      CompleteNegativeRoots (C n) old →
      ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * (C (n + 1)).eval (-old i)) :
    ∀ n, StrictlyInterlaces n := by
  intro n
  by_cases hn : n < 150
  · exact finite n hn
  · have h150 : 150 ≤ n := by omega
    obtain ⟨old, hOld⟩ := roots_from_checkpoints (by omega) (checkpoints n h150)
    exact next_from_old_root_signs hOld (oldRootSigns n h150 old hOld)

end CatalanStrictPeaks
