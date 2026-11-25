import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith

/-!
# A root-spacing step for powers of the Eulerian matrix

For positive, multiplicatively separated roots, the polynomial update
G(x) - a * x * G(x / v) inserts one root in each displayed gap.
-/

namespace EulerianRootSpacing

open Polynomial Set Filter
open scoped BigOperators

noncomputable def rootProduct {m : ℕ} (x : Fin m → ℝ) : ℝ[X] :=
  ∏ i, -(X - C (x i))

noncomputable def spacingStep (G : ℝ[X]) (a v : ℝ) : ℝ[X] :=
  G - C a * X * G.comp (C (v⁻¹) * X)

@[simp] theorem eval_spacingStep (G : ℝ[X]) (a v t : ℝ) :
    (spacingStep G a v).eval t = G.eval t - a * t * G.eval (t / v) := by
  simp only [spacingStep, eval_sub, eval_mul, eval_C, eval_X, eval_comp, div_eq_mul_inv]
  rw [mul_comm (v⁻¹) t]

theorem spacingStep_C_mul (G : ℝ[X]) (a v c : ℝ) :
    spacingStep (C c * G) a v = C c * spacingStep G a v := by
  simp only [spacingStep, mul_comp, C_comp]
  ring

@[simp] private theorem eval_rootProduct {m : ℕ} (x : Fin m → ℝ) (t : ℝ) :
    (rootProduct x).eval t = ∏ i, (x i - t) := by
  rw [rootProduct, eval_prod]
  simp only [eval_neg, eval_sub, eval_X, eval_C, neg_sub]

private theorem rootProduct_degree {m : ℕ} (x : Fin m → ℝ) :
    (rootProduct x).natDegree = m := by
  rw [rootProduct, natDegree_prod]
  · simp only [natDegree_neg, natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp
  · intro i _
    exact neg_ne_zero.mpr (X_sub_C_ne_zero _)

private theorem rootProduct_leadingCoeff {m : ℕ} (x : Fin m → ℝ) :
    (rootProduct x).leadingCoeff = (-1 : ℝ) ^ m := by
  simp only [rootProduct, leadingCoeff_prod, leadingCoeff_neg, leadingCoeff_X_sub_C,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem eval_rootProduct_at_root {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (rootProduct x).eval (x i) = 0 := by
  rw [eval_rootProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

private theorem card_fin_prefix {m k : ℕ} (h : k ≤ m) :
    ((Finset.univ : Finset (Fin m)).filter fun i => i.val < k).card = k := by
  rw [show ((Finset.univ : Finset (Fin m)).filter fun i => i.val < k) =
      (Finset.univ : Finset (Fin k)).map (Fin.castLEEmb h) by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt]
  simp

private theorem product_sign {m : ℕ} {x : Fin m → ℝ} {t : ℝ} {k : ℕ} (hk : k ≤ m)
    (hleft : ∀ i, i.val < k → x i < t) (hright : ∀ i, k ≤ i.val → t < x i) :
    0 < (-1 : ℝ) ^ k * (rootProduct x).eval t := by
  let sign (i : Fin m) : ℝ := if i.val < k then -1 else 1
  have hp : 0 < ∏ i, sign i * (x i - t) := by
    apply Finset.prod_pos
    intro i _
    by_cases hi : i.val < k
    · simp [sign, hi, hleft i hi]
    · simp [sign, hi, sub_pos.mpr (hright i (Nat.le_of_not_gt hi))]
  have hs : ∏ i, sign i = (-1 : ℝ) ^ k := by
    unfold sign
    rw [← Finset.prod_filter]
    simp [card_fin_prefix hk]
  rwa [Finset.prod_mul_distrib, hs, ← eval_rootProduct] at hp

private theorem neg_one_pow_sq (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem eval_prod_neg_of_signed_adjacent {a b : ℝ} {k : ℕ}
    (ha : 0 < (-1 : ℝ) ^ k * a) (hb : 0 < (-1 : ℝ) ^ (k + 1) * b) :
    a * b < 0 := by
  have h := mul_pos ha hb
  have heq : ((-1 : ℝ) ^ k * a) * ((-1 : ℝ) ^ (k + 1) * b) = -(a * b) := by
    calc
      _ = ((-1 : ℝ) ^ k) ^ 2 * (-(a * b)) := by rw [pow_succ]; ring
      _ = _ := by rw [neg_one_pow_sq, one_mul]
  rw [heq] at h
  exact neg_pos.mp h

private theorem exists_root_between {G : ℝ[X]} {l r : ℝ} (hlr : l < r)
    (hs : G.eval l * G.eval r < 0) :
    ∃ y : ℝ, l < y ∧ y < r ∧ G.IsRoot y := by
  rcases mul_neg_iff.mp hs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · obtain ⟨y, hy, hzero⟩ := (intermediate_value_Icc' hlr.le G.continuous.continuousOn)
      (show (0 : ℝ) ∈ Icc (G.eval r) (G.eval l) from ⟨hr.le, hl.le⟩)
    exact ⟨y, lt_of_le_of_ne hy.1 (by rintro rfl; exact hl.ne' hzero),
      lt_of_le_of_ne hy.2 (by rintro rfl; exact hr.ne hzero), hzero⟩
  · obtain ⟨y, hy, hzero⟩ := (intermediate_value_Icc hlr.le G.continuous.continuousOn)
      (show (0 : ℝ) ∈ Icc (G.eval l) (G.eval r) from ⟨hl.le, hr.le⟩)
    exact ⟨y, lt_of_le_of_ne hy.1 (by rintro rfl; exact hl.ne hzero),
      lt_of_le_of_ne hy.2 (by rintro rfl; exact hr.ne' hzero), hzero⟩

private theorem step_degree_and_sign {m : ℕ} (x : Fin m → ℝ) {a v : ℝ}
    (ha : 0 < a) (hv : 1 < v) :
    let Q := spacingStep (rootProduct x) a v
    Q.natDegree = m + 1 ∧ 0 < (-1 : ℝ) ^ (m + 1) * Q.leadingCoeff := by
  dsimp
  let G := rootProduct x
  let V : ℝ[X] := C (v⁻¹) * X
  let N := C a * X * G.comp V
  have hv0 : 0 < v := zero_lt_one.trans hv
  have hGd : G.natDegree = m := rootProduct_degree x
  have hGl : G.leadingCoeff = (-1 : ℝ) ^ m := rootProduct_leadingCoeff x
  have hVd : V.natDegree = 1 := by
    dsimp [V]
    rw [natDegree_C_mul (inv_ne_zero hv0.ne')]
    simp
  have hVl : V.leadingCoeff = v⁻¹ := by
    simp [V, leadingCoeff_mul]
  have hcomp_lc : (G.comp V).leadingCoeff = (-1 : ℝ) ^ m * (v⁻¹) ^ m := by
    rw [leadingCoeff_comp (by rw [hVd]; omega), hGl, hVl, hGd]
  have hcomp_ne : G.comp V ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hcomp_lc]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (inv_ne_zero hv0.ne'))
  have hd : N.natDegree = m + 1 := by
    change (C a * X * G.comp V).natDegree = _
    rw [natDegree_mul (by simp [ha.ne']) hcomp_ne, natDegree_C_mul ha.ne',
      natDegree_X, natDegree_comp, hGd, hVd]
    omega
  have hNlead : N.leadingCoeff = a * (-1 : ℝ) ^ m * (v⁻¹) ^ m := by
    change (C a * X * G.comp V).leadingCoeff = _
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, hcomp_lc]
    ring
  have hlt : G.natDegree < N.natDegree := by rw [hGd, hd]; omega
  have hdegree : (G - N).natDegree = m + 1 :=
    (natDegree_sub_eq_right_of_natDegree_lt hlt).trans hd
  have hlead : (G - N).leadingCoeff = -N.leadingCoeff := by
    rw [leadingCoeff, hdegree, coeff_sub, coeff_eq_zero_of_natDegree_lt (by
      rwa [← hd]), zero_sub, ← hd, coeff_natDegree]
  change (G - N).natDegree = m + 1 ∧ 0 < (-1 : ℝ) ^ (m + 1) * (G - N).leadingCoeff
  refine ⟨hdegree, ?_⟩
  rw [hlead, hNlead]
  calc
    0 < a * (v⁻¹) ^ m := mul_pos ha (pow_pos (inv_pos.mpr hv0) _)
    _ = (-1 : ℝ) ^ (m + 1) * -(a * (-1 : ℝ) ^ m * (v⁻¹) ^ m) := by
      rw [pow_succ]
      calc
        _ = ((-1 : ℝ) ^ m) ^ 2 * (a * (v⁻¹) ^ m) := by rw [neg_one_pow_sq, one_mul]
        _ = _ := by ring

private theorem spacing_signs {m : ℕ} (x : Fin m → ℝ) {a v : ℝ}
    (ha : 0 < a) (hv : 1 < v) (hx : ∀ i, 0 < x i)
    (hspace : ∀ i j : Fin m, i < j → v * x i < x j) :
    let Q := spacingStep (rootProduct x) a v
    0 < Q.eval 0 ∧
      ∀ i : Fin m, 0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (x i) ∧
        0 < (-1 : ℝ) ^ (i.val + 1) * Q.eval (v * x i) := by
  dsimp
  have hv0 : 0 < v := zero_lt_one.trans hv
  have hvx (i : Fin m) : x i < v * x i := by
    nlinarith [mul_pos (sub_pos.mpr hv) (hx i)]
  have hmono : Monotone x := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · rfl
    · exact le_of_lt ((hvx i).trans (hspace i j hij))
  constructor
  · simp only [eval_spacingStep, zero_mul, mul_zero, sub_zero, eval_rootProduct]
    exact Finset.prod_pos (fun i _ => by simpa using hx i)
  · intro i
    have hdiv : x i / v < x i := (div_lt_iff₀ hv0).2 (by simpa [mul_comm] using hvx i)
    have hscaled := product_sign (x := x) (t := x i / v) i.isLt.le
      (fun j hj => (lt_div_iff₀ hv0).2 (by simpa [mul_comm] using hspace j i hj))
      (fun j hj => hdiv.trans_le (hmono hj))
    have hright := product_sign (x := x) (t := v * x i) i.isLt
      (fun j hj => (hmono (by omega : j ≤ i)).trans_lt (hvx i))
      (fun j hj => hspace i j (by omega))
    constructor
    · rw [eval_spacingStep, eval_rootProduct_at_root, zero_sub, pow_succ]
      calc
        0 < a * x i * ((-1 : ℝ) ^ i.val * (rootProduct x).eval (x i / v)) :=
          mul_pos (mul_pos ha (hx i)) hscaled
        _ = _ := by ring
    · rw [eval_spacingStep, mul_div_cancel_left₀ _ hv0.ne', eval_rootProduct_at_root, mul_zero,
        sub_zero]
      exact hright

private theorem exists_far_endpoint {Q : ℝ[X]} {m : ℕ}
    (hd : Q.natDegree = m + 1) (hc : 0 < (-1 : ℝ) ^ (m + 1) * Q.leadingCoeff)
    (l : ℝ) : ∃ r : ℝ, l < r ∧ 0 < (-1 : ℝ) ^ (m + 1) * Q.eval r := by
  let T := C ((-1 : ℝ) ^ (m + 1)) * Q
  have hdeg : 0 < T.degree := by
    apply natDegree_pos_iff_degree_pos.1
    change 0 < (C ((-1 : ℝ) ^ (m + 1)) * Q).natDegree
    rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), hd]
    omega
  have hlead : 0 ≤ T.leadingCoeff := by
    change 0 ≤ (C ((-1 : ℝ) ^ (m + 1)) * Q).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact hc.le
  obtain ⟨r, hr, ht⟩ := ((eventually_gt_atTop l).and
    ((T.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead).eventually_gt_atTop 0)).exists
  exact ⟨r, hr, by simpa [T] using ht⟩

private noncomputable def lowerGap {m : ℕ} (x : Fin m → ℝ) (v : ℝ)
    (i : Fin (m + 1)) : ℝ :=
  if h : i.val = 0 then 0 else v * x ⟨i.val - 1, by omega⟩

/-- The updated polynomial has exactly the indicated roots, counted with multiplicity. -/
theorem spacingStep_roots {m : ℕ} (x : Fin m → ℝ) {a v : ℝ}
    (ha : 0 < a) (hv : 1 < v) (hx : ∀ i, 0 < x i)
    (hspace : ∀ i j : Fin m, i < j → v * x i < x j) :
    let Q := spacingStep (rootProduct x) a v
    ∃ y : Fin (m + 1) → ℝ,
      (∀ i, 0 < y i) ∧
      (∀ i : Fin m, y i.castSucc < x i ∧ v * x i < y i.succ) ∧
      (∀ i j : Fin (m + 1), i < j → v * y i < y j) ∧
      Q.roots = (Finset.univ.image y).val ∧
      ∃ c : ℝ, 0 < c ∧ Q = C c * rootProduct y := by
  classical
  let Q := spacingStep (rootProduct x) a v
  have hv0 : 0 < v := zero_lt_one.trans hv
  have hmono : Monotone x := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · rfl
    · have hs := hspace i j hij
      have hh := mul_pos (sub_pos.mpr hv) (hx i)
      nlinarith
  obtain ⟨hd, hc⟩ := step_degree_and_sign x ha hv
  obtain ⟨hzero, hsign⟩ := spacing_signs x ha hv hx hspace
  have hlower_nonneg (i : Fin (m + 1)) : 0 ≤ lowerGap x v i := by
    unfold lowerGap
    split
    · rfl
    · exact (mul_pos hv0 (hx _)).le
  have hlower_sign (i : Fin (m + 1)) :
      0 < (-1 : ℝ) ^ i.val * Q.eval (lowerGap x v i) := by
    unfold lowerGap
    split
    next hi => simpa [hi, Q] using hzero
    next hi =>
      let j : Fin m := ⟨i.val - 1, by omega⟩
      have hj : j.val + 1 = i.val := by dsimp [j]; omega
      simpa only [hj, Q] using (hsign j).2
  have hchoice (i : Fin (m + 1)) :
      ∃ z : ℝ, lowerGap x v i < z ∧ (∀ hi : i.val < m, z < x ⟨i.val, hi⟩) ∧
        Q.IsRoot z := by
    by_cases hi : i.val < m
    · let j : Fin m := ⟨i.val, hi⟩
      have hab : lowerGap x v i < x j := by
        unfold lowerGap
        split
        · exact hx j
        next hi0 =>
          apply hspace
          show i.val - 1 < i.val
          omega
      have hs : Q.eval (lowerGap x v i) * Q.eval (x j) < 0 :=
        eval_prod_neg_of_signed_adjacent (hlower_sign i) (hsign j).1
      obtain ⟨z, hl, hr, hroot⟩ := exists_root_between hab hs
      exact ⟨z, hl, fun _ => hr, hroot⟩
    · have hieq : i.val = m := by omega
      obtain ⟨r, hr, hs⟩ := exists_far_endpoint hd hc (lowerGap x v i)
      have hpair : Q.eval (lowerGap x v i) * Q.eval r < 0 := by
        apply eval_prod_neg_of_signed_adjacent (hlower_sign i)
        simpa only [hieq] using hs
      obtain ⟨z, hl, _, hroot⟩ := exists_root_between hr hpair
      exact ⟨z, hl, fun hj => (hi hj).elim, hroot⟩
  choose y hy using hchoice
  have hpos (i : Fin (m + 1)) : 0 < y i :=
    (hlower_nonneg i).trans_lt (hy i).1
  have hgap (i : Fin m) : y i.castSucc < x i ∧ v * x i < y i.succ := by
    refine ⟨(hy i.castSucc).2.1 i.isLt, ?_⟩
    have heq : lowerGap x v i.succ = v * x i := by
      unfold lowerGap
      simp [Fin.val_succ]
    rw [← heq]
    exact (hy i.succ).1
  have hsep (i j : Fin (m + 1)) (hij : i < j) : v * y i < y j := by
    let i' : Fin m := ⟨i.val, by omega⟩
    let j' : Fin m := ⟨j.val - 1, by omega⟩
    have hi_eq : i'.castSucc = i := Fin.ext rfl
    have hj_eq : j'.succ = j := by apply Fin.ext; dsimp [j']; omega
    have hij' : i' ≤ j' := by show i.val ≤ j.val - 1; omega
    rw [← hi_eq, ← hj_eq]
    exact (mul_lt_mul_of_pos_left (hgap i').1 hv0).trans_le
      ((mul_le_mul_of_nonneg_left (hmono hij') hv0.le).trans (hgap j').2.le)
  have hinj : Function.Injective y := by
    apply StrictMono.injective
    intro i j hij
    have hh := hsep i j hij
    have hp := mul_pos (sub_pos.mpr hv) (hpos i)
    nlinarith
  let S : Finset ℝ := Finset.univ.image y
  have hcard : S.card = m + 1 := by
    change (Finset.univ.image y).card = _
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnonzero : Q ≠ 0 := by
    intro h
    have hd' : Q.natDegree = m + 1 := hd
    rw [h, natDegree_zero] at hd'
    omega
  have hle : S.val ≤ Q.roots := (Multiset.le_iff_subset S.nodup).2 (by
    intro z hz
    have hmem : z ∈ Finset.univ.image y := hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact (mem_roots hnonzero).2 (hy i).2.2)
  have hall : S.val = Q.roots := Multiset.eq_of_le_of_card_le hle (by
    calc
      Q.roots.card ≤ Q.natDegree := card_roots' Q
      _ = m + 1 := hd
      _ = S.val.card := hcard.symm)
  have hroot_card : Q.roots.card = Q.natDegree := by rw [← hall, hd]; exact hcard
  have hprod : (Q.roots.map fun z => X - C z).prod = ∏ i, (X - C (y i)) := by
    rw [← hall]
    change (∏ z ∈ Finset.univ.image y, (X - C z)) = _
    exact Finset.prod_image (fun _ _ _ _ h => hinj h)
  have hfactor : Q = C Q.leadingCoeff * ∏ i, (X - C (y i)) := by
    have h := (C_leadingCoeff_mul_prod_multiset_X_sub_C hroot_card).symm
    rwa [hprod] at h
  let s := (-1 : ℝ) ^ (m + 1)
  refine ⟨y, hpos, hgap, hsep, hall.symm, s * Q.leadingCoeff, hc, ?_⟩
  have hunit : s ^ 2 = 1 := neg_one_pow_sq (m + 1)
  have hcoefficient : (s * Q.leadingCoeff) * s = Q.leadingCoeff := by
    calc
      _ = s ^ 2 * Q.leadingCoeff := by ring
      _ = _ := by rw [hunit, one_mul]
  have hcast : C s = (-1 : ℝ[X]) ^ (m + 1) := by simp [s]
  calc
    Q = C Q.leadingCoeff * ∏ i, (X - C (y i)) := hfactor
    _ = C (s * Q.leadingCoeff) * rootProduct y := by
      rw [rootProduct, Finset.prod_neg, Finset.card_univ, Fintype.card_fin, ← hcast,
        ← mul_assoc, ← map_mul, hcoefficient]

end EulerianRootSpacing
