import CoarseStarConstants

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def coarseScale : ℕ := 2^32

def coarseLinear (slab : Fin 9) (i : ℕ) : ℕ :=
  if i < 4 then 0 else
    ⌈(coarseScale : ℚ) * rationalDegreeMass (linearSlabK slab) i *
      ((coarseStarNumerator slab : ℚ) / 256) / linearSlabLower slab⌉₊

def coarseLinearArray (slab : Fin 9) : Array ℕ :=
  ((List.range 241).map (coarseLinear slab)).toArray

theorem coarseLinearArray_get (slab : Fin 9) {i : ℕ} (hi : i < 241) :
    (coarseLinearArray slab)[i]! = coarseLinear slab i := by
  have hj : i < ((List.range 241).map (coarseLinear slab)).length := by simpa using hi
  rw [coarseLinearArray, List.getElem!_toArray]
  simp only [getElem!_pos, hj, List.getElem_map, List.getElem_range]

def dotFrom (L Q : Array ℕ) (m : ℕ) : ℕ :=
  (List.range (m+1)).foldl (fun acc i => acc + (i+1)*L[i+1]!*Q[m-i]!) 0

theorem fold_range_sum (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, sum_range_succ, ih]
    rfl

theorem dotFrom_eq (L Q : Array ℕ) (m : ℕ) :
    dotFrom L Q m = ∑ ij ∈ antidiagonal m, (ij.1+1)*L[ij.1+1]!*Q[ij.2]! := by
  unfold dotFrom
  rw [fold_range_sum]
  exact (Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (i+1)*L[i+1]!*Q[j]!) m).symm

def checkRecurrenceBlock (L Q : Array ℕ) (start size : ℕ) : Bool :=
  (List.range size).all (fun i =>
    let m := start+i
    decide (dotFrom L Q m ≤ (m+1)*Q[m+1]!*coarseScale))

theorem recurrence_of_check {L Q : Array ℕ} {start size m : ℕ}
    (h : checkRecurrenceBlock L Q start size = true)
    (hstart : start ≤ m) (hend : m < start+size) :
    ∑ ij ∈ antidiagonal m, (ij.1+1)*L[ij.1+1]!*Q[ij.2]! ≤ (m+1)*Q[m+1]!*coarseScale := by
  unfold checkRecurrenceBlock at h
  have hm : m-start ∈ List.range size := List.mem_range.mpr (by omega)
  have got := List.all_eq_true.mp h (m-start) hm
  have he : start+(m-start) = m := by omega
  simpa only [he, decide_eq_true_eq, dotFrom_eq] using got

def checkLinearBlock (slab : Fin 9) (L : Array ℕ) (start size : ℕ) : Bool :=
  (List.range size).all (fun j =>
    let i := start+j
    decide (L[i]! = coarseLinear slab i))

theorem coarseLinear_of_check {slab : Fin 9} {L : Array ℕ} {start size i : ℕ}
    (h : checkLinearBlock slab L start size = true)
    (hstart : start ≤ i) (hend : i < start+size) :
    L[i]! = coarseLinear slab i := by
  unfold checkLinearBlock at h
  have hi : i-start ∈ List.range size := List.mem_range.mpr (by omega)
  have got := List.all_eq_true.mp h (i-start) hi
  have he : start+(i-start) = i := by omega
  simpa only [he, decide_eq_true_eq] using got

def coarseLift : ℕ := 2^24

theorem coarseScale_lift : coarseLift * coarseScale = linearScale := by rfl

theorem lift_coarse_recurrence {l q : ℕ → ℕ} {m : ℕ}
    (h : ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤
      (m+1)*q (m+1)*coarseScale) :
    ∑ ij ∈ antidiagonal m, (ij.1+1)*(coarseLift*l (ij.1+1))*(coarseLift*q ij.2) ≤
      (m+1)*(coarseLift*q (m+1))*linearScale := by
  have hs :
      (∑ ij ∈ antidiagonal m, (ij.1+1)*(coarseLift*l (ij.1+1))*(coarseLift*q ij.2)) =
        (coarseLift*coarseLift) *
          (∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro ij _
    ring
  rw [hs, ← coarseScale_lift]
  convert Nat.mul_le_mul_left (coarseLift*coarseLift) h using 1 <;> ring

#print axioms coarseLinear_of_check
#print axioms lift_coarse_recurrence
#print axioms dotFrom_eq
#print axioms recurrence_of_check
end OpenMathResearch.LongCycleExcedances
