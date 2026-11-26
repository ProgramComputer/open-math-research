import OpenMathResearch.AlternatingSignRoots
import OpenMathResearch.IntegerLevelNodes

/-!
# Sign count for the three-column balanced-array phase

The analytic proof supplies a continuous normalized phase ending at 2n/3,
an increasing map to positive root moduli, and strict signs at integer phase.
These hypotheses give the exact root count with multiplicity.
-/

namespace BalancedThreeColumnSigns

open Polynomial Set

/-- The phase-band sign tests for degree ⌊2n/3⌋ exhaust all roots of the
reflected polynomial in the positive half-line. The endpoint at 2n/3 is
used to select finite phase nodes. The leading sign supplies the last sample
exactly when one fewer finite node is available. -/
theorem positive_roots_of_phase_signs {n : ℕ} (hn : 0 < n)
    (G : ℝ[X]) (hdegree : G.natDegree = 2 * n / 3)
    (hzero : 0 < G.eval 0)
    (hleading : 0 < (-1 : ℝ) ^ G.natDegree * G.leadingCoeff)
    {p a : ℝ → ℝ} {l r : ℝ} (hlr : l < r)
    (hp : ContinuousOn p (Icc l r)) (hl : p l < 1)
    (hr : p r = 2 * (n : ℝ) / 3)
    (ha : StrictMonoOn a (Ioo l r)) (hapos : ∀ x ∈ Ioo l r, 0 < a x)
    (hsign : ∀ (k : ℕ), 0 < k → ∀ x, x ∈ Ioo l r → p x = k →
      0 < (-1 : ℝ) ^ k * G.eval (a x)) :
    ∃ roots : Fin (2 * n / 3) → ℝ, StrictMono roots ∧
      (∀ i, 0 < roots i) ∧ G.roots = (Finset.univ.image roots).val := by
  let m := (2 * n - 1) / 3
  have hm_lt : 3 * m < 2 * n := by dsimp [m]; omega
  have hm_real : 3 * (m : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hm_lt
  have hm : (m : ℝ) < p r := by rw [hr]; linarith
  obtain ⟨t, ht, hmem, htval⟩ :=
    OpenMathResearch.IntegerLevelNodes.increasing_integer_level_nodes hlr hp hl m hm
  let q (i : Fin m) := a (t i)
  have hq : StrictMono q := fun i j hij => ha (hmem i) (hmem j) (ht hij)
  have hpos (i : Fin m) : 0 < q i := hapos (t i) (hmem i)
  have hqs (i : Fin m) : 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (q i) :=
    hsign (i.val + 1) (Nat.succ_pos _) (t i) (hmem i) (htval i)
  have hmd : 2 * n / 3 = m ∨ 2 * n / 3 = m + 1 := by dsimp [m]; omega
  rcases hmd with hd | hd
  · rw [hd] at hdegree ⊢
    obtain ⟨roots, hmono, hbounds, _, heq⟩ :=
      OpenMathResearch.AlternatingSignRoots.transfer_same_degree G q hdegree hq hpos hzero hqs
    exact ⟨roots, hmono, fun i => (hbounds i).1, heq⟩
  · rw [hd] at hdegree ⊢
    rw [hdegree] at hleading
    obtain ⟨roots, hmono, hpositive, _, heq⟩ :=
      OpenMathResearch.AlternatingSignRoots.transfer_extra_root G q hdegree hq hpos hzero hqs hleading
    exact ⟨roots, hmono, hpositive, heq⟩

end BalancedThreeColumnSigns
