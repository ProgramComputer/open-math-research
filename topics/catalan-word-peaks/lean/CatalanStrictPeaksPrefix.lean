import CatalanStrictPeaksIntervalData

/-!
# Kernel verification of the strict Catalan peak prefix

The data module supplies candidate packed evaluations, coefficients, and
intervals. The kernel verifies the convolution, digit extraction, and
exact interval checks.
-/

namespace CatalanStrictPeaks.Finite

open FastCoefficients OpenMathResearch.OrientedNegativeInterlace

private def checkCertificate (n : ℕ) : Bool :=
  (decide (row last n prefixValues = prefixCoefficients[n]!) &&
    checkRowWithCoefficients denominator n prefixCoefficients[n]! prefixBoxes[n]!) &&
  (if n < last then
    checkStep (base last) prefixValues n && checkPair n prefixBoxes[n]! prefixBoxes[n + 1]!
  else true)

private def checkRange (start length : ℕ) : Bool :=
  (List.range' start length).all checkCertificate

section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Serial kernel checks keep memory bounded as the rows grow.
private theorem checked_000 : checkRange 0 10 = true := by decide +kernel
private theorem checked_010 : checkRange 10 10 = true := by decide +kernel
private theorem checked_020 : checkRange 20 10 = true := by decide +kernel
private theorem checked_030 : checkRange 30 10 = true := by decide +kernel
private theorem checked_040 : checkRange 40 10 = true := by decide +kernel
private theorem checked_050 : checkRange 50 10 = true := by decide +kernel
private theorem checked_060 : checkRange 60 10 = true := by decide +kernel
private theorem checked_070 : checkRange 70 10 = true := by decide +kernel
private theorem checked_080 : checkRange 80 10 = true := by decide +kernel
private theorem checked_090 : checkRange 90 10 = true := by decide +kernel
private theorem checked_100 : checkRange 100 10 = true := by decide +kernel
private theorem checked_110 : checkRange 110 10 = true := by decide +kernel
private theorem checked_120 : checkRange 120 10 = true := by decide +kernel
private theorem checked_130 : checkRange 130 10 = true := by decide +kernel
private theorem checked_140 : checkRange 140 10 = true := by decide +kernel
private theorem checked_150 : checkRange 150 1 = true := by decide +kernel
end

private theorem fold_range (start length : ℕ) :
    (List.range' start length).all checkCertificate = checkRange start length := rfl

private theorem certificates_checked : (List.range (last + 1)).all checkCertificate = true := by
  change (List.range 151).all checkCertificate = true
  have hs : List.range 151 =
      List.range' 0 10 ++
      List.range' 10 10 ++
      List.range' 20 10 ++
      List.range' 30 10 ++
      List.range' 40 10 ++
      List.range' 50 10 ++
      List.range' 60 10 ++
      List.range' 70 10 ++
      List.range' 80 10 ++
      List.range' 90 10 ++
      List.range' 100 10 ++
      List.range' 110 10 ++
      List.range' 120 10 ++
      List.range' 130 10 ++
      List.range' 140 10 ++
      List.range' 150 1 := by decide
  rw [hs]
  simp only [List.all_append, fold_range, checked_000, checked_010, checked_020, checked_030, checked_040,
    checked_050, checked_060, checked_070, checked_080, checked_090,
    checked_100, checked_110, checked_120, checked_130, checked_140,
    checked_150, Bool.and_self]

private theorem certificate_checked (n : ℕ) (hn : n ≤ last) :
    checkCertificate n = true :=
  List.all_eq_true.mp certificates_checked n (List.mem_range.mpr (by omega))

private theorem step_and_pair_checked (n : ℕ) (hn : n < last) :
    checkStep (base last) prefixValues n = true ∧
      checkPair n prefixBoxes[n]! prefixBoxes[n + 1]! = true := by
  have h := (Bool.and_eq_true_iff.mp (certificate_checked n hn.le)).2
  simp only [if_pos hn, Bool.and_eq_true] at h
  exact h

private theorem row_checked (n : ℕ) (hn : n ≤ last) :
    checkRow denominator n prefixBoxes[n]! = true := by
  have h := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (certificate_checked n hn)).1
  have hcoeff := of_decide_eq_true h.1
  have hcorrect := row_eq_coefficients (computed := prefixValues) (by decide)
    (fun i hi => (step_and_pair_checked i hi).1) hn
  simpa only [checkRow, ← hcorrect, hcoeff] using h.2

/-- Rows 0 through 150 have only simple negative roots. -/
theorem roots_through_150 (n : ℕ) (hn : n ≤ 150) :
    ∃ r : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) r := by
  obtain ⟨r, hroots, _⟩ := checkRow_sound (b := denominator) (by decide) (row_checked n hn)
  exact ⟨r, hroots⟩

/-- The first 150 consecutive pairs strictly interlace in the specified orientation. -/
theorem interlacing_before_150 (n : ℕ) (hn : n < 150) : StrictlyInterlaces n := by
  have hp := (step_and_pair_checked n hn).2
  exact checkPair_sound (b := denominator) (by decide) (row_checked n hn.le)
    (row_checked (n + 1) hn) hp

/-- Rows 0 through 20 have only simple negative roots. -/
theorem roots_through_20 (n : ℕ) (hn : n ≤ 20) :
    ∃ r : Fin (rowDegree n) → ℝ, CompleteNegativeRoots (C n) r :=
  roots_through_150 n (by omega)

/-- The first 20 consecutive pairs strictly interlace in the specified orientation. -/
theorem interlacing_before_20 (n : ℕ) (hn : n < 20) : StrictlyInterlaces n :=
  interlacing_before_150 n (by omega)

/-- The remaining analytic hypotheses suffice for strict interlacing at every length. -/
theorem interlacing_from_analytic_signs
    (checkpoints : ∀ n, 150 ≤ n → Checkpoints n)
    (oldRootSigns : ∀ n, 150 ≤ n → ∀ old : Fin (rowDegree n) → ℝ,
      CompleteNegativeRoots (C n) old →
      ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * (C (n + 1)).eval (-old i)) :
    ∀ n, StrictlyInterlaces n :=
  interlacing_from_finite_and_analytic_signs interlacing_before_150 checkpoints oldRootSigns

end CatalanStrictPeaks.Finite
