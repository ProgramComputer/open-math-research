import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Ordered witnesses for integer levels

A continuous real-valued function on a closed interval admits positive
integer-level witnesses in strictly increasing order when its endpoint
values strictly bracket the levels.
-/

namespace OpenMathResearch.IntegerLevelNodes

open Set

private theorem node_between {p : ℝ → ℝ} {l r h : ℝ}
    (hlr : l ≤ r) (hp : ContinuousOn p (Icc l r))
    (hl : p l < h) (hr : h < p r) :
    ∃ x ∈ Ioo l r, p x = h := by
  obtain ⟨x, hx, hpx⟩ := (intermediate_value_Icc hlr hp)
    (show h ∈ Icc (p l) (p r) from ⟨hl.le, hr.le⟩)
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 (by rintro rfl; exact hl.ne hpx),
    lt_of_le_of_ne hx.2 (by rintro rfl; exact hr.ne' hpx)⟩, hpx⟩

/-- Consecutive positive integer levels admit increasing interior witnesses
even when the continuous phase fails to be monotone. -/
theorem increasing_integer_level_nodes {p : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hp : ContinuousOn p (Icc l r))
    (hl : p l < 1) (m : ℕ) (hr : (m : ℝ) < p r) :
    ∃ t : Fin m → ℝ, StrictMono t ∧
      (∀ i, t i ∈ Ioo l r) ∧ (∀ i, p (t i) = ((i.val + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨t, ht, hmem, heval⟩ := ih (by push_cast at hr; linarith)
    cases m with
    | zero =>
      obtain ⟨x, hx, hpx⟩ := node_between hlr.le hp hl (by simpa using hr)
      refine ⟨fun _ => x, ?_, fun _ => hx, ?_⟩
      · intro i j hij
        have heq : i = j := Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega)
        exact (hij.ne heq).elim
      · intro i
        have heq : i = (0 : Fin 1) := Fin.ext (by have hi := i.isLt; omega)
        simpa [heq] using hpx
    | succ m =>
      let tlast := t (Fin.last m)
      have htl : l < tlast := (hmem (Fin.last m)).1
      have htr : tlast < r := (hmem (Fin.last m)).2
      have hlevel : p tlast < ((m + 2 : ℕ) : ℝ) := by
        rw [show p tlast = ((m + 1 : ℕ) : ℝ) from heval (Fin.last m)]
        exact_mod_cast Nat.lt_succ_self (m + 1)
      obtain ⟨x, hx, hpx⟩ := node_between htr.le (hp.mono (Icc_subset_Icc_left htl.le))
        hlevel hr
      refine ⟨Fin.snoc t x, ?_, ?_, ?_⟩
      · apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hx.1
        · have heq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
          simpa only [heq, Fin.snoc_castSucc] using ht (Fin.castSucc_lt_succ j)
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using show x ∈ Ioo l r from ⟨htl.trans hx.1, hx.2⟩
        · simpa using hmem j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [add_assoc] using hpx
        · simpa using heval j

end OpenMathResearch.IntegerLevelNodes
