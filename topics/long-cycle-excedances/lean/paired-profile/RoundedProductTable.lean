import LinearSlabs
import BinIntegerCertificate

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances
open Finset

def qStep (G : ℕ) (l : ℕ → ℕ) (Q : Array ℕ) (m : ℕ) : ℕ :=
  ((∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*Q[ij.2]!)
    +(m+1)*G-1)/((m+1)*G)

/-- The prefix has m+1 entries. Each recurrence step appends exactly one. -/
def qPrefix (G : ℕ) (l : ℕ → ℕ) : ℕ → Array ℕ
  | 0 => #[G]
  | m+1 => let Q := qPrefix G l m; Q.push (qStep G l Q m)

theorem qPrefix_size (G : ℕ) (l : ℕ → ℕ) (m : ℕ) :
    (qPrefix G l m).size = m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [qPrefix, ih]

def roundedQ (G : ℕ) (l : ℕ → ℕ) (b : ℕ) : ℕ := (qPrefix G l b)[b]!

theorem qPrefix_get (G : ℕ) (l : ℕ → ℕ) {m b : ℕ} (h : b ≤ m) :
    (qPrefix G l m)[b]! = roundedQ G l b := by
  induction m with
  | zero =>
    obtain rfl : b=0 := by omega
    rfl
  | succ m ih =>
    by_cases hb : b=m+1
    · subst b
      rfl
    · have hbm : b ≤ m := by omega
      have hlt : b < (qPrefix G l m).size := by rw [qPrefix_size]; omega
      rw [qPrefix]
      simp only [getElem!_pos, Array.size_push, hlt, show b < (qPrefix G l m).size+1 by omega,
        Array.getElem_push_lt]
      simpa only [getElem!_pos, hlt] using ih hbm

theorem roundedQ_zero (G : ℕ) (l : ℕ → ℕ) : roundedQ G l 0 = G := rfl

theorem roundedQ_step (G : ℕ) (l : ℕ → ℕ) (m : ℕ) :
    roundedQ G l (m+1) =
      ((∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*roundedQ G l ij.2)
        +(m+1)*G-1)/((m+1)*G) := by
  have hsize := qPrefix_size G l m
  have hi : m+1 < ((qPrefix G l m).push (qStep G l (qPrefix G l m) m)).size := by
    simp [hsize]
  have hlast : roundedQ G l (m+1) = qStep G l (qPrefix G l m) m := by
    unfold roundedQ
    rw [qPrefix]
    simp only [getElem!_pos, hi]
    simpa only [hsize] using
      (Array.getElem_push_eq (xs := qPrefix G l m) (x := qStep G l (qPrefix G l m) m))
  rw [hlast]
  unfold qStep
  have hsum :
      (∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*(qPrefix G l m)[ij.2]!) =
      ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*roundedQ G l ij.2 := by
    apply sum_congr rfl
    intro ij hij
    have h := mem_antidiagonal.mp hij
    rw [qPrefix_get G l (by omega : ij.2 ≤ m)]
  rw [hsum]

/-- A finite sampler of the linear table is enough for bins through cap. -/
def linearBuffer (j : Fin 9) (cap : ℕ) : Array ℕ :=
  Array.ofFn (fun b : Fin (cap+1) => linearSlabTable j b.val)

def qSlabPrefix (j : Fin 9) (cap : ℕ) : Array ℕ :=
  let l := linearBuffer j cap
  qPrefix linearScale (fun i => l[i]!) cap

theorem qPrefix_congr {G : ℕ} {l₁ l₂ : ℕ → ℕ} {m : ℕ}
    (he : ∀ i ≤ m, l₁ i = l₂ i) : qPrefix G l₁ m = qPrefix G l₂ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hold := ih (fun i hi => he i (by omega))
    simp only [qPrefix, hold]
    unfold qStep
    have hsum :
        (∑ ij ∈ antidiagonal m, (ij.1+1)*l₁ (ij.1+1)*(qPrefix G l₂ m)[ij.2]!) =
        ∑ ij ∈ antidiagonal m, (ij.1+1)*l₂ (ij.1+1)*(qPrefix G l₂ m)[ij.2]! := by
      apply sum_congr rfl
      intro ij hij
      have hij' := mem_antidiagonal.mp hij
      rw [he (ij.1+1) (by omega)]
    rw [hsum]

theorem qSlabPrefix_get (j : Fin 9) {b cap : ℕ} (hb : b ≤ cap) :
    (qSlabPrefix j cap)[b]! = roundedQ linearScale (linearSlabTable j) b := by
  unfold qSlabPrefix
  have he (i : ℕ) (hi : i ≤ cap) :
      (linearBuffer j cap)[i]! = linearSlabTable j i := by
    unfold linearBuffer
    have hg : i < (Array.ofFn (fun x : Fin (cap+1) => linearSlabTable j x.val)).size := by
      simp
      omega
    simp only [getElem!_pos, hg, Array.getElem_ofFn]
  rw [qPrefix_congr he]
  exact qPrefix_get _ _ hb

#print axioms qSlabPrefix_get
#print axioms qPrefix_get
#print axioms roundedQ_step
end OpenMathResearch.LongCycleExcedances
