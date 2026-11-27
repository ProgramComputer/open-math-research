import AnchoredProbability
import LongCycleBounds.AnchoredRows

namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open LongCycles Polynomial Finset

noncomputable def originalProbability (k r : ℕ) : ℝ :=
  (enumerator r k).eval 1 / (r.factorial : ℝ)

theorem originalProbability_spec {k : ℕ} (hk : 2 ≤ k) :
    Spec k (originalProbability k) := by
  classical
  apply from_anchored_polynomials (by omega : 0 < k) (fun r => enumerator r k) eulerian
  · have ha : ∀ σ : Equiv.Perm (Fin 0), Allowed k σ := fun _ x => Fin.elim0 x
    have he : ∀ σ : Equiv.Perm (Fin 0), excedances σ = 0 := by
      intro σ
      simp [excedances]
    simp [enumerator, ha, he, Fintype.card_perm]
  · intro m
    simp [eulerian, eval_finsetSum, Fintype.card_perm]
  · intro r rp
    exact LongCycleBounds.Anchored.anchored_row_recurrence hk (⟨0,rp⟩ : Fin r)

theorem original_upper61 {k r : ℕ} (hk : 13 ≤ k) (hr : 2*k ≤ r) :
    (k : ℝ)*originalProbability k r ≤ 61/100 :=
  upper61 (originalProbability_spec (by omega)) hk r hr

theorem original_upper59 {k r : ℕ} (hk : 22 ≤ k) (hr : 2*k ≤ r) :
    (k : ℝ)*originalProbability k r ≤ 59/100 :=
  upper59 (originalProbability_spec (by omega)) hk r hr

theorem original_upper47 {k r : ℕ} (hk : 100 ≤ k) (hr : 2*k ≤ r) :
    (k : ℝ)*originalProbability k r ≤ 4/7 :=
  upper47 (originalProbability_spec (by omega)) hk r hr

theorem original_lower547 {k r : ℕ} (hk : 2 ≤ k) (hr : 3*k ≤ r) :
    (547/1000 : ℝ) < (k : ℝ)*originalProbability k r :=
  lower547 (originalProbability_spec hk) (by omega) r hr

theorem original_lower548 {k r : ℕ} (hk : 2 ≤ k) (hr : 3*k ≤ r) :
    (548/1000 : ℝ) < (k : ℝ)*originalProbability k r :=
  lower548 (originalProbability_spec hk) (by omega) r hr

#print axioms originalProbability_spec
#print axioms original_upper61
#print axioms original_upper59
#print axioms original_upper47
#print axioms original_lower547
#print axioms original_lower548
end OpenMathResearch.LongCycleExcedances.CycleProbability
