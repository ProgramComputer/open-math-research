import BalancedPairCompression
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Diagonal maximizers on a fixed-product torus

For a complex objective affine in the sum of each pair at fixed pair product,
a squared-modulus maximizer that also maximizes the squared modulus of the
coordinate sum must be diagonal. The balanced-array row polynomial has this
fixed-product affineness.
-/

namespace BalancedTorusMaxima

open scoped BigOperators
open Complex BalancedPairCompression

variable {ι M : Type*} [DecidableEq ι]

def replacePair (x : ι → M) (i j : ι) (u v : M) : ι → M :=
  Function.update (Function.update x j v) i u

@[simp] theorem replacePair_same (x : ι → M) (i j : ι) :
    replacePair x i j (x i) (x j) = x := by
  simp [replacePair]

variable [Fintype ι]

@[to_additive]
theorem prod_replacePair [CommMonoid M] (x : ι → M) (i j : ι) (hij : i ≠ j) (u v : M) :
    ∏ k, replacePair x i j u v k =
      u * v * ∏ k ∈ (Finset.univ.erase i).erase j, x k := by
  let y := replacePair x i j u v
  have hj : j ∈ (Finset.univ : Finset ι).erase i := by
    simp [Ne.symm hij]
  have hi_val : y i = u := by simp [y, replacePair]
  have hj_val : y j = v := by simp [y, replacePair, Ne.symm hij]
  calc
    ∏ k, y k = y i * ∏ k ∈ (Finset.univ : Finset ι).erase i, y k :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    _ = y i * (y j * ∏ k ∈ (Finset.univ.erase i).erase j, y k) := by
      rw [Finset.mul_prod_erase _ _ hj]
    _ = u * v * ∏ k ∈ (Finset.univ.erase i).erase j, x k := by
      rw [hi_val, hj_val, mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := Finset.mem_erase.mp hk
      have hki := (Finset.mem_erase.mp hk'.2).1
      simp [y, replacePair, hki, hk'.1]

def unitProductTorus (p : ℂ) : Set (ι → ℂ) :=
  {x | (∀ i, normSq (x i) = 1) ∧ (∏ i, x i) = p}

theorem replacePair_mem_unitProductTorus {p : ℂ} {x : ι → ℂ}
    (hx : x ∈ unitProductTorus p) {i j : ι} (hij : i ≠ j) {u v : ℂ}
    (hu : normSq u = 1) (hv : normSq v = 1) (hprod : u * v = x i * x j) :
    replacePair x i j u v ∈ unitProductTorus p := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      simpa [replacePair] using hu
    by_cases hkj : k = j
    · subst k
      simpa [replacePair, hki] using hv
    simpa [replacePair, hki, hkj] using hx.1 k
  · rw [prod_replacePair x i j hij, hprod, ← prod_replacePair x i j hij, replacePair_same]
    exact hx.2

/-- Symmetric affine dependence on a pair's sum when its product is fixed. -/
def PairAffine (f : (ι → ℂ) → ℂ) : Prop :=
  ∀ (x : ι → ℂ) (i j : ι), i ≠ j →
    ∃ a b : ℂ, ∀ u v : ℂ, u * v = x i * x j →
      f (replacePair x i j u v) = a + b * (u + v)

/-- The auxiliary coordinate-sum maximum among torus modulus maximizers is diagonal. -/
theorem diagonal_of_two_maxima {f : (ι → ℂ) → ℂ} (hf : PairAffine f)
    {p : ℂ} {x : ι → ℂ} (hx : x ∈ unitProductTorus p)
    (hmax : ∀ y ∈ unitProductTorus p, normSq (f y) ≤ normSq (f x))
    (haux : ∀ y ∈ unitProductTorus p, normSq (f y) = normSq (f x) →
      normSq (∑ k, y k) ≤ normSq (∑ k, x k)) :
    ∀ i j, x i = x j := by
  intro i j
  by_contra hxy
  have hij : i ≠ j := fun h => hxy (congrArg x h)
  obtain ⟨a, b, hab⟩ := hf x i j hij
  have hbase : f x = a + b * (x i + x j) := by
    simpa using hab (x i) (x j) rfl
  have hb : b = 0 := by
    apply slope_eq_zero_at_unit_pair_max (hx.1 i) (hx.1 j) hxy a b
    intro u hu hp
    have h := hmax (replacePair x i j u u)
      (replacePair_mem_unitProductTorus hx hij hu hu (by simpa [pow_two] using hp))
    rwa [hab u u (by simpa [pow_two] using hp), hbase] at h
  let c := ∑ k ∈ (Finset.univ.erase i).erase j, x k
  obtain ⟨u, hu, hp, hlt⟩ := exists_compressing_unit_pair (hx.1 i) (hx.1 j) hxy
    c 1 one_ne_zero
  have hmem := replacePair_mem_unitProductTorus hx hij hu hu (by simpa [pow_two] using hp)
  have hsame : normSq (f (replacePair x i j u u)) = normSq (f x) := by
    rw [hab u u (by simpa [pow_two] using hp), hbase, hb]
    simp
  have hreplace : (∑ k, replacePair x i j u u k) = c + 1 * (u + u) := by
    rw [sum_replacePair x i j hij]
    dsimp [c]
    ring
  have hsum : (∑ k, x k) = c + 1 * (x i + x j) := by
    have h := sum_replacePair x i j hij (x i) (x j)
    rw [replacePair_same] at h
    rw [h]
    dsimp [c]
    ring
  have h := haux (replacePair x i j u u) hmem hsame
  rw [hreplace, hsum] at h
  exact (not_le_of_gt hlt) h

open Polynomial

/-- The balanced-row objective, written in reversed Vieta coefficients. -/
noncomputable def rowObjective (r : ℕ) (x : ι → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (r + 1), (∏ i, (X + C (x i))).coeff (Fintype.card ι - k)

omit [DecidableEq ι] in
theorem rowObjective_eq_elementary_sum (r : ℕ) (hr : r ≤ Fintype.card ι) (x : ι → ℂ) :
    rowObjective r x =
      ∑ k ∈ Finset.range (r + 1), ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, ∏ i ∈ S, x i := by
  unfold rowObjective
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ Fintype.card ι := by
    exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hr
  rw [Finset.prod_X_add_C_coeff Finset.univ x (by simp), Finset.card_univ,
    Nat.sub_sub_self hkd]

private noncomputable def takeRowCoeffs (d r : ℕ) (f : ℂ[X]) : ℂ :=
  ∑ k ∈ Finset.range (r + 1), f.coeff (d - k)

private theorem takeRowCoeffs_add (d r : ℕ) (f g : ℂ[X]) :
    takeRowCoeffs d r (f + g) = takeRowCoeffs d r f + takeRowCoeffs d r g := by
  simp [takeRowCoeffs, Finset.sum_add_distrib]

private theorem takeRowCoeffs_C_mul (d r : ℕ) (a : ℂ) (f : ℂ[X]) :
    takeRowCoeffs d r (C a * f) = a * takeRowCoeffs d r f := by
  simp [takeRowCoeffs, Finset.mul_sum]

theorem pairAffine_rowObjective (r : ℕ) : PairAffine (rowObjective (ι := ι) r) := by
  intro x i j hij
  let d := Fintype.card ι
  let f : ℂ[X] := ∏ k ∈ (Finset.univ.erase i).erase j, (X + C (x k))
  refine ⟨takeRowCoeffs d r ((X ^ 2 + C (x i * x j)) * f),
    takeRowCoeffs d r (X * f), ?_⟩
  intro u v hp
  have hprod : (∏ k, (X + C (replacePair x i j u v k))) =
      (X + C u) * (X + C v) * f := by
    rw [← prod_replacePair (fun k => X + C (x k)) i j hij (X + C u) (X + C v)]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k
      simp [replacePair]
    by_cases hkj : k = j
    · subst k
      simp [replacePair, hki]
    simp [replacePair, hki, hkj]
  change takeRowCoeffs d r (∏ k, (X + C (replacePair x i j u v k))) = _
  rw [hprod]
  have heq : (X + C u) * (X + C v) * f =
      (X ^ 2 + C (x i * x j)) * f + C (u + v) * (X * f) := by
    rw [← hp, map_mul, map_add]
    ring
  rw [heq, takeRowCoeffs_add, takeRowCoeffs_C_mul, mul_comm (u + v)]

end BalancedTorusMaxima
