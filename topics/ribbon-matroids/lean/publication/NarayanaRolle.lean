import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Polynomial
open scoped Polynomial Nat

noncomputable section

namespace Ribbon.Source

private def model (r : ℕ) : ℝ[X] := X ^ (r + 1) * (X - 1) ^ (r + 1)

private def diff (r j : ℕ) : ℝ[X] := derivative^[j] (model r)

private theorem diff_eval (r j : ℕ) (x : ℝ) :
    (diff r j).eval x = ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * ((r + 1).descFactorial (j - k) : ℝ) * ((r + 1).descFactorial k : ℝ) *
      (x ^ (r + 1 - k) * (x - 1) ^ (r + 1 - (j - k))) := by
  rw [diff, model, mul_comm (X ^ (r + 1)), iterate_derivative_mul, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_derivative_X_pow_eq_smul, ← C_1, iterate_derivative_X_sub_pow]
  simp only [eval_smul, eval_mul, eval_pow, eval_X, eval_sub, eval_C]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

private theorem model_monic (r : ℕ) : (model r).Monic :=
  (monic_X_pow _).mul ((monic_X_sub_C (1 : ℝ)).pow _)

private theorem model_natDegree (r : ℕ) : (model r).natDegree = 2 * (r + 1) := by
  unfold model
  rw [← C_1]
  rw [natDegree_mul (monic_X_pow _).ne_zero ((monic_X_sub_C (1 : ℝ)).pow _).ne_zero]
  rw [natDegree_X_pow]
  rw [natDegree_pow, natDegree_X_sub_C]
  omega

private theorem diff_ne_zero {r j : ℕ} (hj : j ≤ r) : diff r j ≠ 0 := by
  intro h
  have hCoef := congrArg (fun p : ℝ[X] => p.coeff (2 * (r + 1) - j)) h
  change (derivative^[j] (model r)).coeff (2 * (r + 1) - j) = (0 : ℝ[X]).coeff _ at hCoef
  rw [coeff_iterate_derivative, show 2 * (r + 1) - j + j = 2 * (r + 1) by omega,
    ← model_natDegree, coeff_natDegree, (model_monic r).leadingCoeff, coeff_zero,
    nsmul_eq_mul, mul_one] at hCoef
  have hd : ((model r).natDegree).descFactorial j ≠ 0 := by
    rw [ne_eq, Nat.descFactorial_eq_zero_iff_lt, model_natDegree]
    omega
  exact (by exact_mod_cast hd : (↑((model r).natDegree.descFactorial j) : ℝ) ≠ 0) hCoef

private theorem diff_endpoint {r j : ℕ} (hj : j ≤ r) :
    (diff r j).IsRoot 0 ∧ (diff r j).IsRoot 1 := by
  constructor
  · change (diff r j).eval 0 = 0
    rw [diff_eval]
    apply Finset.sum_eq_zero
    intro k hk
    have hK : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hp : r + 1 - k ≠ 0 := by omega
    simp [zero_pow hp]
  · change (diff r j).eval 1 = 0
    rw [diff_eval]
    apply Finset.sum_eq_zero
    intro k _
    have hp : r + 1 - (j - k) ≠ 0 := by omega
    simp [zero_pow hp]

/-- Distinct real roots in the closed unit interval. -/
private def boundedRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun x => 0 ≤ x ∧ x ≤ 1)

private theorem mem_boundedRoots {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} :
    x ∈ boundedRoots p ↔ p.IsRoot x ∧ 0 ≤ x ∧ x ≤ 1 := by
  simp [boundedRoots, mem_roots hp]

private theorem boundedRolle {p : ℝ[X]} (hp : p ≠ 0) (hd : p.derivative ≠ 0) :
    (boundedRoots p).card ≤ ((boundedRoots p.derivative) \ (boundedRoots p)).card + 1 := by
  apply Finset.card_le_diff_of_interleaved
  intro x hx y hy hxy hgap
  obtain ⟨hxRoot, hxLower, _⟩ := (mem_boundedRoots hp).mp hx
  obtain ⟨hyRoot, _, hyUpper⟩ := (mem_boundedRoots hp).mp hy
  obtain ⟨z, hz, hzDeriv⟩ := exists_deriv_eq_zero hxy p.continuousOn (hxRoot.trans hyRoot.symm)
  rw [p.deriv] at hzDeriv
  exact ⟨z, (mem_boundedRoots hd).mpr ⟨hzDeriv, hxLower.trans hz.1.le, hz.2.le.trans hyUpper⟩, hz⟩

private theorem endpoints_subset {r j : ℕ} (hj : j ≤ r) :
    ({0, 1} : Finset ℝ) ⊆ boundedRoots (diff r j) := by
  intro x hx
  obtain ⟨h0, h1⟩ := diff_endpoint hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (mem_boundedRoots (diff_ne_zero hj)).mpr ⟨h0, by norm_num, by norm_num⟩
  · exact (mem_boundedRoots (diff_ne_zero hj)).mpr ⟨h1, by norm_num, by norm_num⟩

private theorem boundedRoots_count {r : ℕ} (j : ℕ) (hj : j ≤ r) :
    j + 2 ≤ (boundedRoots (diff r j)).card := by
  induction j with
  | zero =>
      have hc := Finset.card_mono (endpoints_subset hj)
      simpa using hc
  | succ j ih =>
      have hJ : j ≤ r := (Nat.le_succ j).trans hj
      have hdiff : diff r (j + 1) = (diff r j).derivative := Function.iterate_succ_apply' _ _ _
      have hD : (diff r j).derivative ≠ 0 := hdiff ▸ diff_ne_zero hj
      have hR := boundedRolle (diff_ne_zero hJ) hD
      rw [← hdiff] at hR
      let s := boundedRoots (diff r (j + 1))
      let t := boundedRoots (diff r j)
      let u : Finset ℝ := {0, 1}
      have hSub : u ⊆ s := endpoints_subset hj
      have hDiff : s \ t ⊆ s \ u := by
        intro x hx
        obtain ⟨hs, ht⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hs, fun hu => ht (endpoints_subset hJ hu)⟩
      have hRest := Finset.card_mono hDiff
      have hTot := Finset.card_sdiff_add_card_eq_card hSub
      have hU : u.card = 2 := by simp [u]
      have hPrev := ih hJ
      change j + 1 + 2 ≤ s.card
      change t.card ≤ (s \ t).card + 1 at hR
      change j + 2 ≤ t.card at hPrev
      omega

private def interiorRoots (r : ℕ) : Finset ℝ := boundedRoots (diff r r) \ {0, 1}

private theorem interiorRoots_card (r : ℕ) : r ≤ (interiorRoots r).card := by
  have hCount := boundedRoots_count r le_rfl
  have hCard := Finset.card_sdiff_add_card_eq_card (endpoints_subset (r := r) (j := r) le_rfl)
  have hTwo : ({0, 1} : Finset ℝ).card = 2 := by simp
  rw [hTwo] at hCard
  unfold interiorRoots
  omega

private theorem interiorRoots_mem {r : ℕ} {x : ℝ} (hx : x ∈ interiorRoots r) :
    (diff r r).IsRoot x ∧ 0 < x ∧ x < 1 := by
  obtain ⟨hx, hEnds⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hRoot, hlo, hhi⟩ := (mem_boundedRoots (diff_ne_zero le_rfl)).mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hEnds
  exact ⟨hRoot, lt_of_le_of_ne hlo (Ne.symm hEnds.1), lt_of_le_of_ne hhi hEnds.2⟩

private theorem diff_eval_narayana {r : ℕ} {p : ℝ[X]}
    (hDegree : p.natDegree ≤ r)
    (hCoeff : ∀ i : ℕ, (↑(r + 1) : ℝ) * p.coeff i =
      ((r + 1).choose i : ℝ) * ((r + 1).choose (i + 1) : ℝ))
    {x : ℝ} (hx : x ≠ 0) :
    (diff r r).eval x =
      (r.factorial : ℝ) * (↑(r + 1) : ℝ) * (x ^ (r + 1) * (x - 1)) *
        p.eval ((x - 1) / x) := by
  rw [diff_eval, eval_eq_sum_range' (Nat.lt_succ_of_le hDegree), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hSym : (r + 1).choose (r - k) = (r + 1).choose (k + 1) := by
    rw [show r - k = (r + 1) - (k + 1) by omega, Nat.choose_symm (by omega)]
  have hFac : (r.choose k : ℝ) * (k.factorial : ℝ) * ((r - k).factorial : ℝ) =
      (r.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hA : r + 1 - (r - k) = k + 1 := by omega
  have hPow : x ^ (r + 1 - k) * (x - 1) ^ (k + 1) =
      x ^ (r + 1) * (x - 1) * ((x - 1) / x) ^ k := by
    have hExp : r + 1 = r + 1 - k + k := by omega
    rw [div_pow, pow_succ, show x ^ (r + 1) = x ^ (r + 1 - k) * x ^ k by
      rw [← pow_add, ← hExp]]
    field_simp
    ring
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    hSym, hA]
  push_cast
  calc
    _ = ((r.choose k : ℝ) * (k.factorial : ℝ) * ((r - k).factorial : ℝ)) *
        (((r + 1).choose k : ℝ) * ((r + 1).choose (k + 1) : ℝ)) *
        (x ^ (r + 1 - k) * (x - 1) ^ (k + 1)) := by ring
    _ = _ := by
      rw [hFac, hPow, ← hCoeff]
      push_cast
      ring

private theorem eval_zero_of_interiorRoot {r : ℕ} {p : ℝ[X]}
    (hDegree : p.natDegree ≤ r)
    (hCoeff : ∀ i : ℕ, (↑(r + 1) : ℝ) * p.coeff i =
      ((r + 1).choose i : ℝ) * ((r + 1).choose (i + 1) : ℝ))
    {x : ℝ} (hx : x ∈ interiorRoots r) :
    p.eval ((x - 1) / x) = 0 := by
  obtain ⟨hxRoot, hxPos, hxLt⟩ := interiorRoots_mem hx
  have h := diff_eval_narayana hDegree hCoeff (ne_of_gt hxPos)
  rw [show (diff r r).eval x = 0 from hxRoot] at h
  have hNe : (r.factorial : ℝ) * (↑(r + 1) : ℝ) * (x ^ (r + 1) * (x - 1)) ≠ 0 :=
    mul_ne_zero (by positivity) (mul_ne_zero (pow_ne_zero _ (ne_of_gt hxPos)) (sub_ne_zero.mpr (ne_of_lt hxLt)))
  exact (mul_eq_zero.mp h.symm).resolve_left hNe

private theorem transform_injOn (r : ℕ) :
    Set.InjOn (fun x : ℝ => (↑((x - 1) / x) : ℂ)) (interiorRoots r : Set ℝ) := by
  intro x hx y hy h
  have hx' := (interiorRoots_mem (show x ∈ interiorRoots r from hx)).2.1
  have hy' := (interiorRoots_mem (show y ∈ interiorRoots r from hy)).2.1
  have hxy : (x - 1) / x = (y - 1) / y := Complex.ofReal_injective h
  rw [div_eq_div_iff (ne_of_gt hx') (ne_of_gt hy')] at hxy
  nlinarith

/-- A polynomial with Narayana coefficients has only simple negative complex roots. -/
theorem narayana_roots {r : ℕ} {p : ℤ[X]}
    (hCoeff : ∀ i : ℕ, ((r + 1 : ℕ) : ℤ) * p.coeff i =
      ((r + 1).choose i : ℤ) * ((r + 1).choose (i + 1) : ℤ)) :
    (p.map (Int.castRingHom ℂ)).roots.card = r ∧
      ∀ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 →
        z.im = 0 ∧ z.re < 0 ∧ (p.map (Int.castRingHom ℂ)).rootMultiplicity z = 1 := by
  classical
  have hDegree : p.natDegree ≤ r := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hc := hCoeff n
    rw [Nat.choose_eq_zero_of_lt (show r + 1 < n + 1 by omega)] at hc
    simp only [Nat.cast_zero, mul_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left (by positivity)
  have hNe : p ≠ 0 := by
    intro hp
    have hc := hCoeff 0
    rw [hp] at hc
    simp only [coeff_zero, mul_zero, Nat.choose_zero_right, Nat.zero_add, Nat.cast_one,
      one_mul, Nat.choose_one_right] at hc
    exact (by positivity : (0 : ℤ) < ((r + 1 : ℕ) : ℤ)).ne hc
  let q := p.map (Int.castRingHom ℝ)
  let Q := p.map (Int.castRingHom ℂ)
  have hq : q.natDegree ≤ r := natDegree_map_le.trans hDegree
  have hqCoeff (i : ℕ) : (↑(r + 1) : ℝ) * q.coeff i =
      ((r + 1).choose i : ℝ) * ((r + 1).choose (i + 1) : ℝ) := by
    change (↑(r + 1) : ℝ) * (p.map (Int.castRingHom ℝ)).coeff i = _
    rw [coeff_map]
    change (↑(r + 1) : ℝ) * (p.coeff i : ℝ) = _
    exact_mod_cast hCoeff i
  have hQ : Q ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective : Function.Injective (Int.castRingHom ℂ))).mpr hNe
  let transform (x : ℝ) : ℂ := ↑((x - 1) / x)
  let roots := (interiorRoots r).image transform
  have hRootsCard : r ≤ roots.card := by
    dsimp [roots, transform]
    rw [Finset.card_image_of_injOn (transform_injOn r)]
    exact interiorRoots_card r
  have hQMap : Q = q.map Complex.ofRealHom := by
    change p.map (Int.castRingHom ℂ) = (p.map (Int.castRingHom ℝ)).map Complex.ofRealHom
    rw [map_map]
    congr 1
  have hSub : roots.val ⊆ Q.roots := by
    intro w hw
    change w ∈ roots at hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_roots hQ, hQMap]
    exact (show q.IsRoot ((x - 1) / x) from eval_zero_of_interiorRoot hq hqCoeff hx).map Complex.ofRealHom
  have hEq : roots.val = Q.roots := by
    apply Multiset.eq_of_le_of_card_le (Finset.val_le_iff_val_subset.mpr hSub)
    exact (card_roots' Q).trans (natDegree_map_le.trans hDegree) |>.trans hRootsCard
  have hDegreeQ : Q.roots.card ≤ r := (card_roots' Q).trans (natDegree_map_le.trans hDegree)
  constructor
  · exact le_antisymm hDegreeQ (by rw [← hEq]; exact hRootsCard)
  · intro z hz
    have hzQ : z ∈ Q.roots := (mem_roots hQ).mpr (by
      change Q.eval z = 0
      rw [eval_map]
      exact hz)
    rw [← hEq] at hzQ
    have hMem : z ∈ roots := hzQ
    have hOne : Q.rootMultiplicity z = 1 := by
      rw [← count_roots, ← hEq, Multiset.count_eq_one_of_mem roots.nodup hzQ]
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hMem
    have hxI := (interiorRoots_mem hx).2
    exact ⟨Complex.ofReal_im _, by simpa [transform] using div_neg_of_neg_of_pos (sub_neg.mpr hxI.2) hxI.1, hOne⟩

end Ribbon.Source
