import ReflectedLogTail
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

def posLogIndex (n : ℕ) : {q : ℤ // q ≠ 0} := ⟨(n+1:ℕ),by exact_mod_cast Nat.succ_ne_zero n⟩
def negLogIndex (n : ℕ) : {q : ℤ // q ≠ 0} := ⟨Int.negSucc n,by omega⟩

private def logIndexEquiv : (ℕ ⊕ ℕ) ≃ {q : ℤ // q ≠ 0} where
  toFun := Sum.elim posLogIndex negLogIndex
  invFun
    | ⟨.ofNat 0,h⟩ => False.elim (h rfl)
    | ⟨.ofNat (n+1),_⟩ => .inl n
    | ⟨.negSucc n,_⟩ => .inr n
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨m,h⟩
    cases m with
    | ofNat n => cases n with
                 | zero => exact (h rfl).elim
                 | succ n => rfl
    | negSucc n => rfl

theorem reflected_log_reindex (f : {q : ℤ // q ≠ 0} → ℝ) (hf : Summable f) :
    ∑' q, f q = f (negLogIndex 0) +
      ∑' n, (f (posLogIndex n)+f (negLogIndex (n+1))) := by
  let g := f ∘ logIndexEquiv
  have hp : Summable (fun n => f (posLogIndex n)) :=
    hf.comp_injective (logIndexEquiv.injective.comp Sum.inl_injective)
  have hn : Summable (fun n => f (negLogIndex n)) :=
    hf.comp_injective (logIndexEquiv.injective.comp Sum.inr_injective)
  have ht : Summable (fun n => f (negLogIndex (n+1))) := (summable_nat_add_iff 1).mpr hn
  have he := @Summable.tsum_sum ℕ ℕ ℝ _ _ _ _ g hp hn
  rw [←logIndexEquiv.tsum_eq f]
  change (∑' x, g x)=_
  rw [he]
  change (∑' n, f (posLogIndex n))+(∑' n, f (negLogIndex n))=_
  rw [←hn.sum_add_tsum_nat_add 1,hp.tsum_add ht]
  simp only [Finset.sum_range_one]
  ring

/-- Pass a positive reflected logarithm bound to the full signed family. -/
theorem reflected_log_bound_of_pair {f : {q : ℤ // q ≠ 0} → ℝ} (hf : Summable f)
    {h A η : ℝ} (hh : 0 < h) (hA : 0 < A)
    (h0 : f (negLogIndex 0) ≤ 1/(2*A))
    (hpair : ∀ n, f (posLogIndex n)+f (negLogIndex (n+1)) ≤
      reflectedLogWeight h (n+1)/(2*A))
    (hbudget : (1 + ∑' i, reflectedLogWeight h (i+1))/(2*A) ≤ η) :
    (∑' q, f q) ≤ η := by
  have hp : Summable (fun n => f (posLogIndex n)) :=
    hf.comp_injective (logIndexEquiv.injective.comp Sum.inl_injective)
  have hn : Summable (fun n => f (negLogIndex (n+1))) :=
    (summable_nat_add_iff 1).mpr
      (show Summable (fun n => f (negLogIndex n)) from
        hf.comp_injective (logIndexEquiv.injective.comp Sum.inr_injective))
  have hsum := (reflected_log_all hh 0).1
  have he := (hp.add hn).tsum_le_tsum hpair (hsum.div_const (2*A))
  rw [reflected_log_reindex _ hf]
  apply (add_le_add h0 he).trans
  rw [tsum_div_const,←add_div]
  exact hbudget

#print axioms reflected_log_bound_of_pair
end OpenMathResearch.LongCycleExcedances
