import CoarseRecurrence

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def weightedCoefficients (L : Array ℕ) : List ℕ :=
  (L.toList.drop 1).mapIdx (fun i a => (i+1)*a)

def dotSequential (W Q : List ℕ) (m : ℕ) : ℕ :=
  ((W.take (m+1)).zipWith (· * ·) ((Q.take (m+1)).reverse)).sum

theorem dotSequential_eq (L Q : Array ℕ) (m : ℕ)
    (hL : m+2 ≤ L.size) (hQ : m+1 ≤ Q.size) :
    dotSequential (weightedCoefficients L) Q.toList m = dotFrom L Q m := by
  unfold dotSequential
  let f (i : Fin (m+1)) := (i.val+1)*L[i.val+1]!*Q[m-i.val]!
  have hl : (weightedCoefficients L).length = L.size - 1 := by
    simp [weightedCoefficients]
  have hlenL : ((weightedCoefficients L).take (m+1)).length = m+1 := by
    simp only [List.length_take, hl]
    exact min_eq_left (by omega)
  have hlenQ : (Q.toList.take (m+1)).length = m+1 := by
    simp only [List.length_take, Array.length_toList]
    exact min_eq_left hQ
  have hz :
      ((weightedCoefficients L).take (m+1)).zipWith (· * ·)
        ((Q.toList.take (m+1)).reverse) = List.ofFn f := by
    apply List.ext_getElem
    · simp [List.length_zipWith, hlenL, hlenQ]
    · intro i hi hi'
      have him : i < m+1 := by simpa using hi'
      have hil : i+1 < L.size := by omega
      have hiq : m-i < Q.size := by omega
      unfold f
      simp only [List.getElem_zipWith, List.getElem_ofFn, List.getElem_take,
        weightedCoefficients, List.getElem_mapIdx, List.getElem_drop,
        List.getElem_reverse, hlenQ, Nat.add_sub_cancel, Array.getElem_toList, getElem!_pos, hil, hiq]
      simp only [Nat.add_comm 1 i]
  rw [hz, List.sum_ofFn, dotFrom, fold_range_sum]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (i+1)*L[i+1]!*Q[m-i]!) (m+1)

def checkSequentialBlock (L Q : Array ℕ) (start size : ℕ) : Bool :=
  let W := weightedCoefficients L
  let q := Q.toList
  (List.range size).all (fun i =>
    let m := start+i
    decide (dotSequential W q m ≤ (m+1)*Q[m+1]!*coarseScale))

theorem recurrence_of_sequential_check {L Q : Array ℕ} {start size m : ℕ}
    (h : checkSequentialBlock L Q start size = true)
    (hstart : start ≤ m) (hend : m < start+size) (hL : m+2 ≤ L.size) (hQ : m+1 ≤ Q.size) :
    ∑ ij ∈ antidiagonal m, (ij.1+1)*L[ij.1+1]!*Q[ij.2]! ≤ (m+1)*Q[m+1]!*coarseScale := by
  unfold checkSequentialBlock at h
  have hm : m-start ∈ List.range size := List.mem_range.mpr (by omega)
  have got := List.all_eq_true.mp h (m-start) hm
  have he : start+(m-start) = m := by omega
  simpa only [he, decide_eq_true_eq, dotSequential_eq L Q m hL hQ, dotFrom_eq] using got

#print axioms dotSequential_eq
#print axioms recurrence_of_sequential_check
end OpenMathResearch.LongCycleExcedances
