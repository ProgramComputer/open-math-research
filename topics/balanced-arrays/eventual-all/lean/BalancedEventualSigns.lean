import BalancedEventual
import OpenMathResearch.AlternatingSignRoots
import Mathlib.Algebra.Polynomial.FieldDivision

namespace BalancedEventual

open Polynomial
open OpenMathResearch.AlternatingSignRoots

private theorem complexOfReal_injective : Function.Injective Complex.ofRealHom := by
  intro x y h
  exact congrArg Complex.re h

/-- Viewing a complete list of distinct negative real roots over the complex
numbers preserves the list and makes the derivative test for simplicity explicit. -/
theorem simpleNegativeRoots_of_real_root_list {m : ℕ} {G : ℝ[X]}
    {r : Fin m → ℝ} (hdegree : G.natDegree = m) (hne : G ≠ 0)
    (hinj : Function.Injective r) (hneg : ∀ i, r i < 0)
    (hroots : G.roots = (Finset.univ.image r).val) :
    HasSimpleNegativeRoots (G.map Complex.ofRealHom) m := by
  classical
  let P := G.map Complex.ofRealHom
  let R : Fin m → ℂ := fun i => Complex.ofRealHom (r i)
  have hPne : P ≠ 0 := (Polynomial.map_ne_zero_iff complexOfReal_injective).mpr hne
  have hcard : G.roots.card = G.natDegree := by
    rw [hroots, hdegree]
    change (Finset.univ.image r).card = m
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmap : G.roots.map Complex.ofRealHom = P.roots :=
    roots_map_of_injective_of_card_eq_natDegree complexOfReal_injective hcard
  have hnodup : P.roots.Nodup := by
    rw [← hmap, hroots]
    exact (Finset.univ.image r).nodup.map complexOfReal_injective
  have hroot (z : ℂ) : P.IsRoot z ↔ ∃ i, R i = z := by
    rw [← mem_roots hPne, ← hmap, hroots]
    simp [Multiset.mem_map, R]
  refine ⟨R, complexOfReal_injective.comp hinj, ?_, hroot⟩
  intro i
  refine ⟨rfl, hneg i, ?_⟩
  intro hder
  have hmultiple := (one_lt_rootMultiplicity_iff_isRoot hPne).mpr
    ⟨(hroot (R i)).mpr ⟨i, rfl⟩, hder⟩
  rw [← count_roots] at hmultiple
  exact (not_lt_of_ge (Multiset.nodup_iff_count_le_one.mp hnodup (R i))) hmultiple

/-- The balanced polynomial before extending scalars to the complex numbers. -/
noncomputable def realArrayPolynomial (n d r : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (arrayCount n d r k : ℝ) * X ^ k

theorem map_realArrayPolynomial (n d r : ℕ) :
    (realArrayPolynomial n d r).map Complex.ofRealHom = arrayPolynomial n d r := by
  change (Polynomial.mapRingHom Complex.ofRealHom) _ = _
  simp [realArrayPolynomial, arrayPolynomial, map_sum]

/-- A complete sign mesh suffices uniformly for any balanced array polynomial.
The mesh is in increasing order on the negative axis. Its last point may be zero.
The sign convention reads positive at the rightmost point, as in the paper. -/
theorem balanced_simpleNegativeRoots_of_sign_mesh {n d r : ℕ}
    (hd : 0 < d) (hr : r ≤ d)
    (t : Fin (n * r / d + 1) → ℝ) (ht : StrictMono t) (hnonpos : ∀ i, t i ≤ 0)
    (hs : ∀ i, 0 < (-1 : ℝ) ^ (n * r / d + i.val) *
      (realArrayPolynomial n d r).eval (t i)) :
    HasSimpleNegativeRoots (arrayPolynomial n d r) (n * r / d) := by
  let m := n * r / d
  let G := realArrayPolynomial n d r
  let H := C ((-1 : ℝ) ^ m) * G
  have hunit : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdegree : G.natDegree = m := by
    rw [← natDegree_map_eq_of_injective complexOfReal_injective G]
    exact (congrArg natDegree (map_realArrayPolynomial n d r)).trans
      (natDegree_arrayPolynomial hd hr)
  have hHdeg : H.natDegree = m := (natDegree_C_mul hunit).trans hdegree
  have hGne : G ≠ 0 := by
    intro h
    simpa [G, h] using hs (0 : Fin (m + 1))
  have hsign (i : Fin (m + 1)) : 0 < (-1 : ℝ) ^ i.val * H.eval (t i) := by
    simpa only [H, eval_mul, eval_C, ← mul_assoc, ← pow_add, Nat.add_comm i.val m]
      using hs i
  obtain ⟨roots, hmono, hbetween, hroots⟩ :=
    roots_of_alternating_sign_mesh H t hHdeg ht hsign
  have hGroot : G.roots = (Finset.univ.image roots).val := by
    simpa only [H, roots_C_mul G hunit] using hroots
  rw [← map_realArrayPolynomial]
  exact simpleNegativeRoots_of_real_root_list hdegree hGne hmono.injective
    (fun i => (hbetween i).2.trans_le (hnonpos i.succ)) hGroot

theorem balanced_simpleNegativeRoots_of_degree_zero {n d r : ℕ}
    (hd : 0 < d) (hr : r ≤ d) (hzero : n * r / d = 0) :
    HasSimpleNegativeRoots (arrayPolynomial n d r) (n * r / d) := by
  apply balanced_simpleNegativeRoots_of_sign_mesh hd hr (fun _ => 0)
  · intro i j hij
    have h : i.val < j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro i
    exact le_rfl
  · intro i
    have hi : i.val = 0 := by have h := i.isLt; omega
    simp only [hzero, hi, Nat.zero_add, pow_zero, one_mul, ← coeff_zero_eq_eval_zero]
    have hcoeff := coeff_arrayPolynomial (n := n) (k := 0) hd hr
    rw [← map_realArrayPolynomial, coeff_map] at hcoeff
    have hreal : (realArrayPolynomial n d r).coeff 0 = (arrayCount n d r 0 : ℝ) := by
      simpa using congrArg Complex.re hcoeff
    rw [hreal]
    exact_mod_cast arrayCount_pos_of_le_degree (n := n) hd hr (Nat.zero_le _)

/-- The remaining analytic input for the uniform eventual theorem. -/
def EventualAlternatingSignMesh : Prop :=
  ∃ N : ℕ, ∀ n d r : ℕ, N ≤ n → 2 ≤ d → 1 ≤ r → r ≤ d → 0 < n * r / d →
    ∃ t : Fin (n * r / d + 1) → ℝ, StrictMono t ∧ (∀ i, t i ≤ 0) ∧
      (∀ i, 0 < (-1 : ℝ) ^ (n * r / d + i.val) *
        (realArrayPolynomial n d r).eval (t i))

theorem eventualClaim_of_alternating_sign_mesh
    (h : EventualAlternatingSignMesh) : EventualClaim := by
  obtain ⟨N, hN⟩ := h
  refine ⟨⟨N, ?_⟩, arrayPolynomial_one_column⟩
  intro n d r hn hd hr hrd
  have hd' : 0 < d := by omega
  by_cases hdegree : 0 < n * r / d
  · obtain ⟨t, ht, hnonpos, hs⟩ := hN n d r hn hd hr hrd hdegree
    exact balanced_simpleNegativeRoots_of_sign_mesh hd' hrd t ht hnonpos hs
  · exact balanced_simpleNegativeRoots_of_degree_zero hd' hrd (Nat.eq_zero_of_not_pos hdegree)

#print axioms simpleNegativeRoots_of_real_root_list
#print axioms map_realArrayPolynomial
#print axioms balanced_simpleNegativeRoots_of_sign_mesh
#print axioms balanced_simpleNegativeRoots_of_degree_zero
#print axioms eventualClaim_of_alternating_sign_mesh

end BalancedEventual
