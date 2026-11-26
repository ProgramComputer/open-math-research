import AuditReferenceSpecs
import CatalanStrictPeaks

namespace AuditReference

open Finset Polynomial

theorem wordConditionsAgree {n : ℕ} (w : BoundedWord n) :
    IsCatalan w ↔ CatalanStrictPeaks.IsCatalan w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have h0 : 0 < n := by simpa [hi] using i.isLt
      have he : (⟨0,h0⟩ : Fin n) = i := Fin.ext hi.symm
      simpa only [he] using h.1 h0
    · intro i j hj
      have hnext : i.val+1 < n := hj ▸ j.isLt
      have he : (⟨i.val+1,hnext⟩ : Fin n) = j := Fin.ext hj.symm
      simpa only [he] using h.2 i.val hnext
  · intro h
    exact ⟨fun h0 => h.1 ⟨0,h0⟩ rfl,
      fun i hn => h.2 ⟨i, lt_trans (Nat.lt_succ_self i) hn⟩ ⟨i+1,hn⟩ rfl⟩

theorem peakCountsAgree {n : ℕ} (w : BoundedWord n) :
    peakCount w = (CatalanStrictPeaks.peaks w).card := by
  unfold peakCount
  congr 1
  ext i
  simp only [CatalanStrictPeaks.peaks, mem_filter, mem_range]
  by_cases h : i+2 < n
  · have hi : i < n := by omega
    have hj : i+1 < n := by omega
    have hr : i < n-2 := by omega
    have hh : CatalanStrictPeaks.HasPeakAt w i ↔
        (w ⟨i,hi⟩).val < (w ⟨i+1,hj⟩).val ∧ (w ⟨i+2,h⟩).val < (w ⟨i+1,hj⟩).val := by
      change (i+2<n ∧
        (if h' : i<n then (w ⟨i,h'⟩).val else 0) <
        (if h' : i+1<n then (w ⟨i+1,h'⟩).val else 0) ∧
        (if h' : i+2<n then (w ⟨i+2,h'⟩).val else 0) <
        (if h' : i+1<n then (w ⟨i+1,h'⟩).val else 0)) ↔ _
      simp [h, hi, hj]
    simp [h, hi, hr, hh]
  · have hr : ¬ i < n-2 := by omega
    simp [h, hr]

theorem catalanPolynomial_eq (n : ℕ) :
    catalanPolynomial n = CatalanStrictPeaks.C n := by
  classical
  unfold catalanPolynomial CatalanStrictPeaks.C CatalanStrictPeaks.words
  have hs : (Finset.univ : Finset (BoundedWord n)).filter IsCatalan =
      Finset.univ.filter CatalanStrictPeaks.IsCatalan := by
    ext w
    simp [wordConditionsAgree]
  rw [hs]
  exact Finset.sum_congr rfl fun w _ => by rw [peakCountsAgree]

#print axioms catalanPolynomial_eq

end AuditReference
