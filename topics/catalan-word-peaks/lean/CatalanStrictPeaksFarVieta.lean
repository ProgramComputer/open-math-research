import OpenMathResearch.OrientedNegativeInterlace
import Mathlib.RingTheory.Polynomial.Vieta

open Polynomial
open OpenMathResearch.OrientedNegativeInterlace

namespace CatalanStrictPeaks.FarEdge

private lemma esymm_one_sum (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map, Function.comp_def]

private lemma twice_esymm_two (s : Multiset ℝ) :
    s.sum ^ 2 = (s.map (fun t => t^2)).sum + 2*s.esymm 2 := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
    have h : (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
      rw [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add]
      congr 1
      rw [Multiset.map_map, ← esymm_one_sum s, Multiset.esymm]
      simp only [Function.comp_def, Multiset.prod_cons]
      rw [← Multiset.sum_map_mul_left]
    simp only [Multiset.sum_cons, Multiset.map_cons, h]
    nlinarith only [ih]

private lemma shifted_factorization {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) :
    P.comp (X + 1) = C P.leadingCoeff * ∏ i, (X + C (1 + r i)) := by
  classical
  have hi : Function.Injective (fun i => -r i) := neg_injective.comp h.2.1.injective
  have hc : P.roots.card = P.natDegree := by
    rw [h.2.2.2, h.1]
    change (Finset.univ.image (fun i => -r i)).card = m
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [h.2.2.2] at hf
  change C P.leadingCoeff * (∏ i ∈ Finset.univ.image (fun j => -r j), (X - C i)) = P at hf
  rw [Finset.prod_image (fun _ _ _ _ heq => hi heq)] at hf
  conv_lhs => rw [← hf]
  rw [mul_comp, C_comp, prod_comp]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [sub_comp, add_assoc]

/-- The two upper coefficients of the translated polynomial measure the sum
and the sum of squares of the translated root moduli. -/
theorem shifted_top_two {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (hm : 2 ≤ m) :
    let Q := P.comp (X + 1)
    Q.coeff (m-1) = P.leadingCoeff * (∑ i, (1 + r i)) ∧
    2 * Q.coeff (m-2) = P.leadingCoeff *
      ((∑ i, (1 + r i))^2 - ∑ i, (1 + r i)^2) := by
  classical
  dsimp only
  let v : Multiset ℝ := Finset.univ.val.map (fun i : Fin m => 1 + r i)
  have hc : v.card = m := by simp [v]
  have hva : v.sum = ∑ i, (1 + r i) := rfl
  have hvb : (v.map (fun b => b^2)).sum = ∑ i, (1 + r i)^2 := by
    simp only [v, Multiset.map_map]; rfl
  have hf : (∏ i, (X + C (1 + r i))) = (v.map (fun a => X + C a)).prod := by
    simp only [v, Multiset.map_map]; rfl
  rw [shifted_factorization h, hf, coeff_C_mul, coeff_C_mul]
  rw [Multiset.prod_X_add_C_coeff v (show m-1 ≤ v.card by omega),
      Multiset.prod_X_add_C_coeff v (show m-2 ≤ v.card by omega)]
  rw [hc, show m-(m-1)=1 by omega, show m-(m-2)=2 by omega, esymm_one_sum, hva]
  constructor
  · rfl
  · have hs := twice_esymm_two v
    rw [hva, hvb] at hs
    rw [show (∑ i, (1 + r i))^2 - ∑ i, (1 + r i)^2 = 2*v.esymm 2 by linarith only [hs]]
    ring


/-- Two coefficient bounds separate the largest root from every competitor. -/
theorem far_root_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (hm : 2 ≤ m) (lead : 0 < P.leadingCoeff)
    {U c : ℝ} (hU : 0 < U)
    (hu : (P.comp (X + 1)).coeff (m-1) = P.leadingCoeff * U)
    (hc : 2*(P.comp (X + 1)).coeff (m-2) < P.leadingCoeff * (c*U^2))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (1-c)*U < 1+r l ∧ 1+r l ≤ U ∧
    ∀ i, i ≠ l → 1+r i < c*U := by
  classical
  obtain ⟨hs, hsq⟩ := shifted_top_two h hm
  let y := fun i : Fin m => 1+r i
  have hy (i : Fin m) : 0 ≤ y i := by dsimp [y]; linarith [h.2.2.1 i]
  have hsum : ∑ i, y i = U := (mul_left_cancel₀ lead.ne' (hs.symm.trans hu))
  change 2 * _ = P.leadingCoeff * ((∑ i, y i)^2 - ∑ i, y i ^ 2) at hsq
  rw [hsum] at hsq
  have hsq' : U^2 - ∑ i, y i^2 < c * U^2 :=
    (mul_lt_mul_left lead).mp (hsq.symm.trans_lt hc)
  have hmax : ∑ i, y i^2 ≤ y l * U := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [sq]
    exact mul_le_mul_of_nonneg_right (show y i ≤ y l from add_le_add_left (last i) 1) (hy i)
  have hL : (1-c)*U < y l := by
    apply (mul_lt_mul_right hU).mp
    nlinarith only [hsq', hmax]
  have hle : y l ≤ U := by
    rw [← hsum]; exact Finset.single_le_sum (fun i _ => hy i) (Finset.mem_univ l)
  refine ⟨hL, hle, ?_⟩
  intro i hi
  have hlo := Finset.sum_erase_add Finset.univ y (Finset.mem_univ l)
  have hi' : i ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have bound : y i ≤ ∑ j ∈ Finset.univ.erase l, y j :=
    Finset.single_le_sum (fun j _ => hy j) hi'
  rw [hsum] at hlo
  change y i < c*U
  nlinarith only [hL, hlo, bound]


theorem eval_at_neg_eq_product {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (x : ℝ) :
    P.eval (-x) = P.leadingCoeff * ∏ i, (r i-x) := by
  have hv := congrArg (fun f : ℝ[X] => f.eval (-x-1)) (shifted_factorization h)
  simp only [eval_comp, eval_add, eval_X, eval_one, sub_add_cancel, eval_mul, eval_C,
    eval_prod] at hv
  convert hv using 2
  apply Finset.prod_congr rfl
  intro i _
  ring

private theorem reflection_product {m : ℕ} (r : Fin m → ℝ) (x : ℝ) :
    (-1 : ℝ)^m * (∏ i, (r i-x)) = ∏ i, (x-r i) := by
  calc
    _ = (∏ _ : Fin m, (-1 : ℝ)) * (∏ i, (r i-x)) := by simp
    _ = ∏ i, ((-1 : ℝ) * (r i-x)) := Finset.prod_mul_distrib.symm
    _ = _ := by apply Finset.prod_congr rfl; intro i _; ring

theorem eval_outside_all {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (lead : 0 < P.leadingCoeff) {x : ℝ}
    (hout : ∀ i, r i < x) : 0 < (-1 : ℝ)^m * P.eval (-x) := by
  rw [eval_at_neg_eq_product h, mul_left_comm, reflection_product]
  exact mul_pos lead (Finset.prod_pos fun i _ => sub_pos.mpr (hout i))

theorem eval_inside_last {m : ℕ} {P : ℝ[X]} {r : Fin (m+1) → ℝ}
    (h : CompleteNegativeRoots P r) (lead : 0 < P.leadingCoeff) {x : ℝ}
    (hlo : ∀ i : Fin m, r i.castSucc < x) (hhi : x < r (Fin.last m)) :
    0 < (-1 : ℝ)^m * P.eval (-x) := by
  rw [eval_at_neg_eq_product h, Fin.prod_univ_castSucc, mul_left_comm]
  rw [← mul_assoc ((-1 : ℝ)^m), reflection_product (fun i : Fin m => r i.castSucc) x]
  exact mul_pos lead (mul_pos (Finset.prod_pos fun i _ => sub_pos.mpr (hlo i)) (sub_pos.mpr hhi))

theorem eval_inside_first {m : ℕ} {P : ℝ[X]} {r : Fin (m+1) → ℝ}
    (h : CompleteNegativeRoots P r) (lead : 0 < P.leadingCoeff) {x : ℝ}
    (hlo : r 0 < x) (hhi : ∀ i : Fin m, x < r i.succ) : P.eval (-x) < 0 := by
  rw [eval_at_neg_eq_product h, Fin.prod_univ_succ]
  exact mul_neg_of_pos_of_neg lead (mul_neg_of_neg_of_pos (sub_neg.mpr hlo)
    (Finset.prod_pos fun i _ => sub_pos.mpr (hhi i)))

theorem shifted_leading {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) : (P.comp (X+1)).coeff m = P.leadingCoeff := by
  classical
  rw [shifted_factorization h, coeff_C_mul, Finset.prod_X_add_C_coeff _ _
    (show m ≤ (Finset.univ : Finset (Fin m)).card by simp)]
  simp

noncomputable def oddFirst (x : ℝ) : ℝ := x*(x+1)*(x+4)*(x+5)/12
noncomputable def oddSecond (x : ℝ) : ℝ :=
  (x-1)*x*(x+1)*(x+2)*(x+5)*(x+6)*(x+7)*(x+8)/2880
noncomputable def evenLead (x : ℝ) : ℝ := (x+1)*(x+4)/2
noncomputable def evenFirst (x : ℝ) : ℝ :=
  x*(x+1)*(x+2)*(x+5)*(x+6)*(x+7)/144
noncomputable def evenSecond (x : ℝ) : ℝ :=
  (x-1)*x*(x+1)*(x+2)*(x+3)*(x+6)*(x+7)*(x+8)*(x+9)*(x+10)/86400

theorem odd_spread {x : ℝ} (hx : 74 ≤ x) :
    50*oddSecond x < 3*(oddFirst x)^2 := by
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  unfold oddSecond oddFirst
  apply sub_pos.mp
  ring_nf
  positivity

theorem even_spread {x : ℝ} (hx : 74 ≤ x) :
    50*evenSecond x*evenLead x < 7*(evenFirst x)^2 := by
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  unfold evenSecond evenFirst evenLead
  apply sub_pos.mp
  ring_nf
  positivity

/-- The neighboring odd-row sums are between four and six times the
translated even-row sum. -/
theorem neighboring_scales {x : ℝ} (hx : 74 ≤ x) :
    let E := evenFirst x / evenLead x
    4*E < oddFirst x ∧ oddFirst x < 6*E ∧
    4*E < oddFirst (x+1) ∧ oddFirst (x+1) < 6*E := by
  dsimp only
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  have h : 0 < evenLead (74+u) := by unfold evenLead; positivity
  simp only [← mul_div_assoc, div_lt_iff₀ h, lt_div_iff₀ h]
  unfold oddFirst evenFirst evenLead
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply sub_pos.mp <;> ring_nf <;> positivity

/-- The three highest coefficients after translating the variable by one. -/
structure ShiftedTop (P : ℝ[X]) (m : ℕ) (L A B : ℝ) : Prop where
  top : (P.comp (X+1)).coeff m = L
  first : (P.comp (X+1)).coeff (m-1) = A
  second : (P.comp (X+1)).coeff (m-2) = B

private theorem bounds_of_top {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (hm : 2 ≤ m)
    {L A B c : ℝ} (top : ShiftedTop P m L A B) (hL : 0 < L) (hA : 0 < A)
    (spread : 50*B*L < c*A^2) (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (1-c/25)*(A/L) < 1+r l ∧ 1+r l ≤ A/L ∧
    ∀ i, i ≠ l → 1+r i < (c/25)*(A/L) := by
  have lc := (shifted_leading h).symm.trans top.top
  apply far_root_bounds h hm (by rwa [lc]) (div_pos hA hL) _ _ l last
  · rw [top.first, lc]
    field_simp
  · rw [top.second, lc]
    have hx : B < c*A^2 / (50*L) := (lt_div_iff₀ (by positivity)).mpr (by linarith only [spread])
    calc 2*B < 2*(c*A^2 / (50*L)) := by linarith only [hx]
         _ = _ := by field_simp; ring

private theorem odd_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (hm : 74 ≤ m)
    (top : ShiftedTop P m 1 (oddFirst m) (oddSecond m))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (22/25 : ℝ)*oddFirst m < 1+r l ∧ 1+r l ≤ oddFirst m ∧
    ∀ i, i ≠ l → 1+r i < (3/25 : ℝ)*oddFirst m := by
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hp : 0 < oddFirst m := by unfold oddFirst; positivity
  have hspread := odd_spread hx
  simpa only [div_one, show 1-(3:ℝ)/25=22/25 by norm_num] using
    bounds_of_top h (by omega) top (by norm_num) hp ((by simpa using hspread) :
      50*oddSecond m*1 < 3*(oddFirst m)^2) l last

private theorem even_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (h : CompleteNegativeRoots P r) (hm : 74 ≤ m)
    (top : ShiftedTop P m (evenLead m) (evenFirst m) (evenSecond m))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (18/25 : ℝ)*(evenFirst m / evenLead m) < 1+r l ∧
    1+r l ≤ evenFirst m / evenLead m ∧
    ∀ i, i ≠ l → 1+r i < (7/25 : ℝ)*(evenFirst m / evenLead m) := by
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0:ℝ)<m := by linarith
  have hp : 0 < evenFirst m := by unfold evenFirst; positivity
  have hl : 0 < evenLead m := by unfold evenLead; positivity
  simpa only [show 1-(7:ℝ)/25=18/25 by norm_num] using
    bounds_of_top h (by omega) top hl hp (even_spread hx) l last

/-- From an odd old row, the next even row has constant leading sign at
the old farthest root. -/
theorem odd_to_even_sign {m : ℕ} (hm : 74 ≤ m) {O E : ℝ[X]} {o e : Fin m → ℝ}
    (ho : CompleteNegativeRoots O o) (he : CompleteNegativeRoots E e)
    (to' : ShiftedTop O m 1 (oddFirst m) (oddSecond m))
    (te : ShiftedTop E m (evenLead m) (evenFirst m) (evenSecond m))
    (l : Fin m) (last : ∀ i : Fin m, i ≤ l) :
    0 < (-1 : ℝ)^m * E.eval (-(o l)) := by
  have topO := odd_bounds ho hm to' l (fun i => ho.2.1.monotone (last i))
  have topE := even_bounds he hm te l (fun i => he.2.1.monotone (last i))
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have scales := neighboring_scales hx
  have hEL : 0 < evenLead m := by unfold evenLead; positivity
  apply eval_outside_all he (by rwa [(shifted_leading he).symm.trans te.top])
  intro i
  have hroot : e i ≤ e l := he.2.1.monotone (last i)
  have hpos := he.2.2.1 l
  linarith only [hroot, hpos, topO.1, topE.2.1, scales.1]

/-- From an even old row, exactly one new odd-row modulus lies beyond the
old farthest root. -/
theorem even_to_odd_sign {m : ℕ} (hm : 74 ≤ m) {E O : ℝ[X]}
    {e : Fin m → ℝ} {o : Fin (m+1) → ℝ} (he : CompleteNegativeRoots E e)
    (ho : CompleteNegativeRoots O o)
    (te : ShiftedTop E m (evenLead m) (evenFirst m) (evenSecond m))
    (to' : ShiftedTop O (m+1) 1 (oddFirst (m+1)) (oddSecond (m+1)))
    (l : Fin m) (last : ∀ i : Fin m, i ≤ l) :
    0 < (-1 : ℝ)^m * O.eval (-(e l)) := by
  have topE := even_bounds he hm te l (fun i => he.2.1.monotone (last i))
  have to2 : ShiftedTop O (m+1) 1 (oddFirst ((m+1 : ℕ) : ℝ)) (oddSecond ((m+1 : ℕ) : ℝ)) := by
    simpa using to'
  have topO := odd_bounds ho (show 74 ≤ m+1 by omega) to2 (Fin.last m)
      (fun i => ho.2.1.monotone (Fin.le_last i))
  simp only [Nat.cast_add, Nat.cast_one] at topO
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have scales := neighboring_scales hx
  apply eval_inside_last ho (by rw [← shifted_leading ho, to'.top]; norm_num)
  · intro i
    have hn := topO.2.2 i.castSucc (Fin.castSucc_ne_last i)
    linarith only [hn, topE.1, scales.2.2.2]
  · have hpos := he.2.2.1 l
    linarith only [hpos, topO.1, topE.2.1, scales.2.2.1]

end CatalanStrictPeaks.FarEdge
