import ReflectedLogSum
import DiscreteOddTail
import PrimitivePoleKernel

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def positiveOddMoment (c : ℝ) (i : ℕ) : ℝ :=
  (2*(i:ℝ)+3)*oWeight c (2*(i:ℝ)+3)

private theorem positiveMoment_nonneg (c : ℝ) (i : ℕ) : 0 ≤ positiveOddMoment c i :=
  mul_nonneg (by positivity) (inv_nonneg.mpr (Even.pow_nonneg (by decide) _))

def firstMomentBound (c : ℝ) (J : ℕ) : ℝ :=
  2*(∑ i ∈ range J, positiveOddMoment c i)+oTail c (2*(J:ℝ)+1)/(190*c)

private theorem positiveMoment_tail {c : ℝ} (hc : 0 < c) (J : ℕ)
    (hg : 1 ≤ 3*c*(2*(J:ℝ)+1)^2) :
    Summable (positiveOddMoment c) ∧
      (∑' i, positiveOddMoment c (i+J)) ≤ oTail c (2*(J:ℝ)+1)/(380*c) := by
  have hb (M:ℕ) : (∑ i ∈ range M, positiveOddMoment c (i+J)) ≤ oTail c (2*(J:ℝ)+1)/(380*c) := by
    have hh := odd_tail_finite_prefix hc (by linarith [Nat.cast_nonneg (α:=ℝ) J] : 1 ≤ 2*(J:ℝ)+1) hg M
    convert hh using 1
    apply sum_congr rfl
    intro i _
    unfold positiveOddMoment
    push_cast
    rw [show 2*((i:ℝ)+J)+3=(2*(J:ℝ)+1)+2*((i:ℝ)+1) by ring]
  exact ⟨(summable_nat_add_iff J).mp (summable_of_sum_range_le (fun i => positiveMoment_nonneg c _) hb),
    Real.tsum_le_of_sum_range_le (fun i => positiveMoment_nonneg c _) hb⟩

/-- The moment for any finite signed-pole set omitting both principal poles.
At J=31 the explicit half-head is precisely the positive odd indices 3 through 63. -/
theorem finite_nonprincipal_first_moment {c : ℝ} (hc : 0 < c) (J : ℕ)
    (hg : 1 ≤ 3*c*(2*(J:ℝ)+1)^2) (T : Finset ℤ) (h0 : 0 ∉ T) (hm : (-1:ℤ) ∉ T) :
    (∑ q ∈ T, |primitiveOddNumber q| *oWeight c (primitiveOddNumber q)) ≤ firstMomentBound c J := by
  classical
  let g (q:ℤ) := |primitiveOddNumber q| *oWeight c (primitiveOddNumber q)
  let B := T.subtype (· ≠ 0)
  let f (q : {q:ℤ // q≠0}) := if q ∈ B then g q else 0
  have hsum : HasSum f (∑ q ∈ B, f q) :=
    hasSum_sum_of_ne_finset_zero (fun q h => by simp [f,h])
  have heq : (∑ q ∈ B, f q) = ∑ q ∈ T, g q := by
    rw [show (∑ q ∈ B, f q)=∑ q ∈ B, g q by exact sum_congr rfl (fun q hq => if_pos hq)]
    exact sum_subtype_of_mem _ (fun q hq h => h0 (h ▸ hq))
  change (∑ q ∈ T,g q) ≤ _
  rw [←heq,←hsum.tsum_eq,reflected_log_reindex _ hsum.summable]
  have hneg : f (negLogIndex 0)=0 := by simp [f,B,negLogIndex,hm]
  rw [hneg,zero_add]
  have hi (q : {q:ℤ // q≠0}) : f q ≤ g q := by
    by_cases h : q ∈ B
    · rw [show f q = g q by simp [f,h]]
    · rw [show f q=0 by simp [f,h]]
      exact mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (Even.pow_nonneg (by decide) _))
  have hpair (i:ℕ) : f (posLogIndex i)+f (negLogIndex (i+1)) ≤
      2*positiveOddMoment c i := by
    apply (add_le_add (hi _) (hi _)).trans_eq
    have hp : primitiveOddNumber (posLogIndex i) = 2*(i:ℝ)+3 := by
      simp [primitiveOddNumber,posLogIndex]; ring
    have hn : primitiveOddNumber (negLogIndex (i+1)) = -(2*(i:ℝ)+3) := by
      simp [primitiveOddNumber,negLogIndex]; ring
    simp only [g,hp,hn,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 2*(i:ℝ)+3),
      positiveOddMoment,oWeight,oBase,neg_sq]
    exact (two_mul _).symm
  obtain ⟨hs,ht⟩ := positiveMoment_tail hc J hg
  have hsf := hsum.summable
  have ha : Summable (fun i => f (posLogIndex i)) := hsf.comp_injective (by
    intro i j h; have := congrArg Subtype.val h; simp [posLogIndex] at this; omega)
  have hb : Summable (fun i => f (negLogIndex (i+1))) := hsf.comp_injective (by
    intro i j h; have := congrArg Subtype.val h; simp [negLogIndex] at this; omega)
  have h := (ha.add hb).tsum_le_tsum hpair (hs.mul_left 2)
  rw [tsum_mul_left,←hs.sum_add_tsum_nat_add J] at h
  apply h.trans
  unfold firstMomentBound
  have hc' : 2*(oTail c (2*(J:ℝ)+1)/(380*c))=oTail c (2*(J:ℝ)+1)/(190*c) := by ring
  linarith only [ht,hc']

#print axioms finite_nonprincipal_first_moment
end OpenMathResearch.LongCycleExcedances
