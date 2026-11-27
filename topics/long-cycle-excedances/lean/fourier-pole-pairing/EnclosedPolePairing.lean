import FourierAnchoredLogistic
import LiteralDiscretePoleMoments
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit

open Finset Complex
open scoped Real
open OpenMathResearch.LongCycleExcedances

/-- Number of positive-imaginary odd poles with modulus below R, provided
the principal pole is enclosed. -/
def enclosedPositiveCount (s R : ℝ) : ℕ :=
  ⌈(Real.sqrt (R^2-s^2)/π-1)/2⌉₊

private theorem pairing_pole_im (s : ℝ) (l : ℤ) :
    (fourierRowPole s l).im = (2*(l:ℝ)+1)*π := by
  simp [fourierRowPole,Complex.add_im,Complex.mul_re,Complex.add_re]

private theorem row_pole_index_injective (s : ℝ) : Function.Injective (fourierRowPole s) := by
  intro i j h
  have hi := congrArg Complex.im h
  rw [pairing_pole_im, pairing_pole_im] at hi
  have hu := mul_right_cancel₀ Real.pi_ne_zero hi
  have hcast : (i:ℝ) = j := by linarith only [hu]
  exact_mod_cast hcast

private theorem row_pole_index_conj (s : ℝ) (j : ℤ) :
    (starRingEnd ℂ) (fourierRowPole s j) = fourierRowPole s (-j-1) := by
  apply Complex.ext
  · simp [fourierRowPole,Complex.conj_re,Complex.add_re,Complex.mul_re,Complex.mul_im]
  · rw [Complex.conj_im, pairing_pole_im,pairing_pole_im]
    push_cast
    ring

private theorem reflected_pole_norm (s : ℝ) (i : ℕ) :
    ‖fourierRowPole s (-(i:ℤ)-1)‖ = ‖fourierRowPole s i‖ := by
  rw [← row_pole_index_conj,Complex.norm_conj]

/-- A strict modulus cutoff is the exact natural-ceiling cutoff on positive
indices. The formula remains correct if a nonprincipal pole is on the circle. -/
theorem positive_enclosed_pole_index {s R : ℝ}
    (hprincipal : ‖fourierRowPole s 0‖ < R) (i : ℕ) :
    i < enclosedPositiveCount s R ↔ ‖fourierRowPole s (i:ℤ)‖ < R := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hprincipal
  have hp0 : 0 ≤ ‖fourierRowPole s 0‖ := norm_nonneg _
  have hprincipalsq : ‖fourierRowPole s 0‖^2 < R^2 :=
    (sq_lt_sq₀ hp0 hR.le).2 hprincipal
  have he := literal_pole_norm_sq s 0
  change ‖fourierRowPole s 0‖^2 = s^2+((2*((0:ℤ):ℝ)+1)*π)^2 at he
  norm_num at he
  rw [he] at hprincipalsq
  have hδ : 0 ≤ R^2-s^2 := by nlinarith only [hprincipalsq,sq_nonneg π]
  have hsq := literal_pole_norm_sq s (i:ℤ)
  change ‖fourierRowPole s (i:ℤ)‖^2 = s^2+((2*(((i:ℕ):ℤ):ℝ)+1)*π)^2 at hsq
  rw [Int.cast_natCast] at hsq
  have hprod : 0 ≤ (2*(i:ℝ)+1)*π := by positivity
  have hn := norm_nonneg (fourierRowPole s (i:ℤ))
  unfold enclosedPositiveCount
  rw [Nat.lt_ceil, ← sq_lt_sq₀ hn hR.le, hsq]
  have hcast :
      (i:ℝ) < (Real.sqrt (R^2-s^2)/π-1)/2 ↔
        (2*(i:ℝ)+1)*π < Real.sqrt (R^2-s^2) := by
    constructor
    · intro h
      apply (lt_div_iff₀ Real.pi_pos).1
      linarith only [h]
    · intro h
      have ht := (lt_div_iff₀ Real.pi_pos).2 h
      linarith only [ht]
  rw [hcast,← sq_lt_sq₀ hprod (Real.sqrt_nonneg _), Real.sq_sqrt hδ]
  constructor <;> intro h <;> linarith only [h]

/-- The exact finite positive half of the enclosed set is the image of its
natural-ceiling prefix. -/
theorem enclosed_positive_half {s R : ℝ} (P : Finset ℂ)
    (hprincipal : ‖fourierRowPole s 0‖ < R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ Set.range (fourierRowPole s) ∧ ‖p‖ < R) :
    P.filter (fun p => 0 < p.im) =
      (Finset.range (enclosedPositiveCount s R)).image (fun i : ℕ => fourierRowPole s (i:ℤ)) := by
  classical
  ext p
  rw [Finset.mem_filter,Finset.mem_image]
  constructor
  · intro h
    obtain ⟨⟨l, rfl⟩,hR⟩ := (hP p).1 h.1
    rw [pairing_pole_im] at h
    have hpos : 0 < 2*(l:ℝ)+1 := pos_of_mul_pos_left h.2 Real.pi_pos.le
    have hl : 0 ≤ l := by
      by_contra! hh
      have h' : (l:ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
      linarith only [hpos,h']
    have hi : (l.toNat:ℤ) = l := Int.toNat_of_nonneg hl
    refine ⟨l.toNat,Finset.mem_range.2 ((positive_enclosed_pole_index hprincipal _).2 ?_),?_⟩
    · rwa [hi]
    · rw [hi]
  · rintro ⟨i,hi,rfl⟩
    refine ⟨(hP _).2 ⟨⟨(i:ℤ), rfl⟩,
      (positive_enclosed_pole_index hprincipal _).1 (Finset.mem_range.1 hi)⟩,?_⟩
    rw [pairing_pole_im,Int.cast_natCast]
    exact mul_pos (by positivity) Real.pi_pos

/-- A stock enclosed-minor finite set with the weak-enclosure membership
rule is exactly the strict range at every regular radius. -/
theorem enclosed_minor_indices_eq_range {s R : ℝ} (indices : Finset ℕ)
    (hprincipal : ‖fourierRowPole s 0‖ < R)
    (hregular : ∀ j : ℤ, ‖fourierRowPole s j‖ ≠ R)
    (hmem : ∀ i : ℕ, i ∈ indices ↔ ‖fourierRowPole s ((i+1:ℕ):ℤ)‖ ≤ R) :
    indices = Finset.range (enclosedPositiveCount s R-1) := by
  ext i
  rw [hmem, Finset.mem_range]
  have hweak : ‖fourierRowPole s ((i+1:ℕ):ℤ)‖ ≤ R ↔
      ‖fourierRowPole s ((i+1:ℕ):ℤ)‖ < R :=
    ⟨fun h => lt_of_le_of_ne h (hregular _), le_of_lt⟩
  rw [hweak, ← positive_enclosed_pole_index hprincipal (i+1)]
  omega

/-- Split the exact enclosed pole set into two disjoint signed halves and
pair conjugate terms. The principal term is index zero, and the remaining
positive terms use i+1 for i below the exact cutoff minus one. -/
theorem enclosed_poles_conjugate_pairing {s R : ℝ} (P : Finset ℂ)
    (hprincipal : ‖fourierRowPole s 0‖ < R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ Set.range (fourierRowPole s) ∧ ‖p‖ < R)
    (g : ℂ → ℂ)
    (hg : ∀ p ∈ P, g ((starRingEnd ℂ) p) = (starRingEnd ℂ) (g p)) :
    (∑ p ∈ P, g p) =
      ((2*(g (fourierRowPole s 0) +
        ∑ i ∈ Finset.range (enclosedPositiveCount s R-1),
          g (fourierRowPole s ((i+1:ℕ):ℤ))).re : ℝ):ℂ) := by
  classical
  let N := enclosedPositiveCount s R
  let p (i : ℕ) := fourierRowPole s (i:ℤ)
  let q (i : ℕ) := fourierRowPole s (-(i:ℤ)-1)
  let A := (Finset.range N).image p
  let B := (Finset.range N).image q
  have hpmap : Function.Injective p :=
    (row_pole_index_injective s).comp Nat.cast_injective
  have hqmap : Function.Injective q := by
    intro i j hij
    have hd := row_pole_index_injective s hij
    change -(i:ℤ)-1 = -(j:ℤ)-1 at hd
    omega
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.2
    intro w hwA hwB
    obtain ⟨i,_,hi⟩ := Finset.mem_image.1 hwA
    obtain ⟨j,_,hj⟩ := Finset.mem_image.1 hwB
    have hd := row_pole_index_injective s (hi.trans hj.symm)
    change (i:ℤ) = -(j:ℤ)-1 at hd
    omega
  have hPpos (i : ℕ) (hi : i ∈ Finset.range N) : p i ∈ P :=
    (hP _).2 ⟨⟨(i:ℤ),rfl⟩,
      (positive_enclosed_pole_index hprincipal _).1 (Finset.mem_range.1 hi)⟩
  have heq : P = A ∪ B := by
    ext w
    rw [Finset.mem_union]
    constructor
    · intro hw
      obtain ⟨⟨l,rfl⟩,hR⟩ := (hP w).1 hw
      cases l with
      | ofNat i =>
        exact Or.inl (Finset.mem_image.2 ⟨i,Finset.mem_range.2
          ((positive_enclosed_pole_index hprincipal _).2 hR),rfl⟩)
      | negSucc i =>
        have hi : Int.negSucc i = -(i:ℤ)-1 := by omega
        rw [hi,reflected_pole_norm] at hR
        exact Or.inr (Finset.mem_image.2 ⟨i,Finset.mem_range.2
          ((positive_enclosed_pole_index hprincipal _).2 hR),by simp only [q,hi]⟩)
    · rintro (hw | hw)
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hw
        exact hPpos i hi
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hw
        apply (hP _).2
        refine ⟨⟨-(i:ℤ)-1,rfl⟩,?_⟩
        change ‖fourierRowPole s (-(i:ℤ)-1)‖ < R
        rw [reflected_pole_norm]
        exact (positive_enclosed_pole_index hprincipal _).1 (Finset.mem_range.1 hi)
  have hS :
      (∑ i ∈ Finset.range N, g (q i)) =
          (starRingEnd ℂ) (∑ i ∈ Finset.range N, g (p i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hg _ (hPpos i hi)]
    congr 1
    exact (row_pole_index_conj s (i:ℤ)).symm
  have hN : 0 < N := (positive_enclosed_pole_index hprincipal 0).2 hprincipal
  have hsplit : (∑ i ∈ Finset.range N, g (p i)) =
      g (p 0) + ∑ i ∈ Finset.range (N-1), g (p (i+1)) := by
    conv_lhs => rw [show N = (N-1)+1 by omega,Finset.sum_range_succ']
    rw [add_comm]
  rw [heq,Finset.sum_union hab]
  change (∑ w ∈ (Finset.range N).image p, g w) +
    (∑ w ∈ (Finset.range N).image q, g w) = _
  rw [Finset.sum_image (fun _ _ _ _ eq => hpmap eq),
    Finset.sum_image (fun _ _ _ _ eq => hqmap eq), hS, Complex.add_conj, hsplit]
  rfl

/-- The real half-sum form of the finite conjugate pairing. Its minor
index range depends only on s and R, independently of the term. -/
theorem enclosed_poles_real_half {s R : ℝ} (P : Finset ℂ)
    (hprincipal : ‖fourierRowPole s 0‖ < R)
    (hP : ∀ p : ℂ, p ∈ P ↔ p ∈ Set.range (fourierRowPole s) ∧ ‖p‖ < R)
    (g : ℂ → ℂ)
    (hg : ∀ p ∈ P, g ((starRingEnd ℂ) p) = (starRingEnd ℂ) (g p)) :
    (∑ p ∈ P, g p).re/2 =
      (g (fourierRowPole s 0)).re +
        (∑ i ∈ Finset.range (enclosedPositiveCount s R-1),
          g (fourierRowPole s ((i+1:ℕ):ℤ))).re := by
  have h := congrArg Complex.re (enclosed_poles_conjugate_pairing P hprincipal hP g hg)
  simp only [Complex.ofReal_re,Complex.add_re] at h
  linarith only [h]

#print axioms enclosed_poles_real_half
#print axioms positive_enclosed_pole_index
#print axioms enclosed_positive_half
#print axioms enclosed_minor_indices_eq_range
#print axioms enclosed_poles_conjugate_pairing
end RepositoryQuotientAudit
