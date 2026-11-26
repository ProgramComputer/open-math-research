import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith

/-!
# Complete polynomial root counts from alternating signs

The mesh and sign-transfer lemmas isolate all roots, counted with
multiplicity, when the number of gaps agrees with the polynomial degree.
-/

namespace OpenMathResearch.AlternatingSignRoots

open Polynomial Set Filter

private theorem opposite_signs {a b : ℝ} {k : ℕ}
    (ha : 0 < (-1 : ℝ) ^ k * a) (hb : 0 < (-1 : ℝ) ^ (k + 1) * b) :
    a * b < 0 := by
  have hs : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have h := mul_pos ha hb
  have heq : ((-1 : ℝ) ^ k * a) * ((-1 : ℝ) ^ (k + 1) * b) = -(a * b) := by
    calc
      _ = ((-1 : ℝ) ^ k) ^ 2 * (-(a * b)) := by rw [pow_succ]; ring
      _ = _ := by rw [hs, one_mul]
  rw [heq] at h
  exact neg_pos.mp h

private theorem root_between {G : ℝ[X]} {l r : ℝ} (hlr : l < r)
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

/-- For a nonzero polynomial, a list of as many distinct roots as the degree exhausts the root multiset. -/
theorem roots_of_complete_list {m : ℕ} (G : ℝ[X]) (r : Fin m → ℝ)
    (hdegree : G.natDegree = m) (hne : G ≠ 0) (hinj : Function.Injective r)
    (hr : ∀ i, G.IsRoot (r i)) : G.roots = (Finset.univ.image r).val := by
  classical
  let R : Finset ℝ := Finset.univ.image r
  have hcard : R.card = m := by
    change (Finset.univ.image r).card = _
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : R.val ≤ G.roots := (Multiset.le_iff_subset R.nodup).2 (by
    intro y hy
    have hmem : y ∈ Finset.univ.image r := hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    exact (mem_roots hne).2 (hr i))
  exact (Multiset.eq_of_le_of_card_le hsub (by
    calc
      G.roots.card ≤ G.natDegree := card_roots' G
      _ = m := hdegree
      _ = R.val.card := hcard.symm)).symm

/-- Alternating signs on a strictly increasing mesh isolate all the roots,
counted with multiplicity, when the number of gaps equals the degree. -/
theorem roots_of_alternating_sign_mesh {m : ℕ} (G : ℝ[X]) (t : Fin (m + 1) → ℝ)
    (hdegree : G.natDegree = m) (ht : StrictMono t)
    (hs : ∀ i, 0 < (-1 : ℝ) ^ i.val * G.eval (t i)) :
    ∃ r : Fin m → ℝ, StrictMono r ∧
      (∀ i, t i.castSucc < r i ∧ r i < t i.succ) ∧
      G.roots = (Finset.univ.image r).val := by
  classical
  have hchoice (i : Fin m) : ∃ y : ℝ, t i.castSucc < y ∧ y < t i.succ ∧ G.IsRoot y := by
    apply root_between (ht (Fin.castSucc_lt_succ i))
    apply opposite_signs (k := i.val)
    · simpa using hs i.castSucc
    · simpa using hs i.succ
  choose r hr using hchoice
  have hrmono : StrictMono r := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by
      show i.val + 1 ≤ j.val
      omega
    exact (hr i).2.1.trans_le ((ht.monotone hle).trans (hr j).1.le)
  have hne : G ≠ 0 := by
    intro h
    simpa [h] using hs (0 : Fin (m+1))
  exact ⟨r, hrmono, fun i => ⟨(hr i).1, (hr i).2.1⟩,
    roots_of_complete_list G r hdegree hne hrmono.injective (fun i => (hr i).2.2)⟩

private theorem cons_zero_mono {m : ℕ} (q : Fin m → ℝ)
    (hq : StrictMono q) (hpos : ∀ i, 0 < q i) :
    StrictMono (Fin.cons 0 q) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  cases m with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hpos (0 : Fin (m+1))
    · have heq : j.succ.castSucc = j.castSucc.succ := Fin.ext rfl
      simpa only [heq, Fin.cons_succ] using hq (Fin.castSucc_lt_succ j)

private theorem snoc_mono {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    {b : ℝ} (hb : t (Fin.last m) < b) : StrictMono (Fin.snoc t b) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hb
  · have heq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
    simpa only [heq, Fin.snoc_castSucc] using ht (Fin.castSucc_lt_succ j)

private theorem cons_signed {m : ℕ} (q : Fin m → ℝ) (G : ℝ[X])
    (hzero : 0 < G.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (q i)) :
    ∀ i : Fin (m + 1), 0 < (-1 : ℝ) ^ i.val * G.eval (Fin.cons (α := fun _ => ℝ) 0 q i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hzero
  · simpa using hs j

private theorem far_sign {G : ℝ[X]} {m : ℕ}
    (hdegree : G.natDegree = m + 1)
    (hleading : 0 < (-1 : ℝ) ^ (m + 1) * G.leadingCoeff) (a : ℝ) :
    ∃ b : ℝ, a < b ∧ 0 < (-1 : ℝ) ^ (m + 1) * G.eval b := by
  let H := C ((-1 : ℝ) ^ (m + 1)) * G
  have hdegreeH : 0 < H.degree := by
    apply natDegree_pos_iff_degree_pos.1
    change 0 < (C ((-1 : ℝ) ^ (m + 1)) * G).natDegree
    rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), hdegree]
    omega
  have hleadingH : 0 ≤ H.leadingCoeff := by
    change 0 ≤ (C ((-1 : ℝ) ^ (m + 1)) * G).leadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_C]
    exact hleading.le
  obtain ⟨b, hb, hh⟩ := ((eventually_gt_atTop a).and
    ((H.tendsto_atTop_of_leadingCoeff_nonneg hdegreeH hleadingH).eventually_gt_atTop 0)).exists
  exact ⟨b, hb, by simpa [H] using hh⟩

/-- Transfer positive test points to the case with one test point per degree. -/
theorem transfer_same_degree {m : ℕ} (G : ℝ[X]) (q : Fin m → ℝ)
    (hdegree : G.natDegree = m) (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (hzero : 0 < G.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (q i)) :
    ∃ r : Fin m → ℝ, StrictMono r ∧ (∀ i, 0 < r i ∧ r i < q i) ∧
      (∀ i j, i < j → q i < r j) ∧ G.roots = (Finset.univ.image r).val := by
  let t : Fin (m + 1) → ℝ := Fin.cons 0 q
  have ht : StrictMono t := cons_zero_mono q hq hpos
  obtain ⟨r, hrmono, hr, hroots⟩ :=
    roots_of_alternating_sign_mesh G t hdegree ht (cons_signed q G hzero hs)
  refine ⟨r, hrmono, ?_, ?_, hroots⟩
  · intro i
    have hnonneg : 0 ≤ t i.castSucc := by
      have hle := ht.monotone (Fin.zero_le i.castSucc)
      simpa [t] using hle
    exact ⟨hnonneg.trans_lt (hr i).1, by simpa [t] using (hr i).2⟩
  · intro i j hij
    have hle : i.succ ≤ j.castSucc := by
      show i.val + 1 ≤ j.val
      omega
    exact (show q i ≤ t j.castSucc by simpa [t] using ht.monotone hle).trans_lt (hr j).1

/-- Transfer positive test points to the case of one extra degree, with a last root
past the largest test point. The leading sign is in the reflected variable. -/
theorem transfer_extra_root {m : ℕ} (G : ℝ[X]) (q : Fin m → ℝ)
    (hdegree : G.natDegree = m + 1) (hq : StrictMono q) (hpos : ∀ i, 0 < q i)
    (hzero : 0 < G.eval 0) (hs : ∀ i, 0 < (-1 : ℝ) ^ (i.val + 1) * G.eval (q i))
    (hleading : 0 < (-1 : ℝ) ^ (m + 1) * G.leadingCoeff) :
    ∃ r : Fin (m + 1) → ℝ, StrictMono r ∧ (∀ i, 0 < r i) ∧
      (∀ i : Fin m, r i.castSucc < q i ∧ q i < r i.succ) ∧
      G.roots = (Finset.univ.image r).val := by
  let t₀ : Fin (m + 1) → ℝ := Fin.cons 0 q
  obtain ⟨b, hb, hbs⟩ := far_sign hdegree hleading (t₀ (Fin.last m))
  let t : Fin (m + 2) → ℝ := Fin.snoc t₀ b
  have ht : StrictMono t := snoc_mono t₀ (cons_zero_mono q hq hpos) hb
  have hts (i : Fin (m + 2)) : 0 < (-1 : ℝ) ^ i.val * G.eval (t i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [t] using hbs
    · simpa [t, t₀] using cons_signed q G hzero hs j
  have htz : t 0 = 0 := by
    change t ((0 : Fin (m + 1)).castSucc) = 0
    simp only [t, t₀, Fin.snoc_castSucc, Fin.cons_zero]
  obtain ⟨r, hrmono, hr, hroots⟩ := roots_of_alternating_sign_mesh G t hdegree ht hts
  refine ⟨r, hrmono, ?_, ?_, hroots⟩
  · intro i
    have hnonneg : 0 ≤ t i.castSucc := by
      rw [← htz]
      exact ht.monotone (Fin.zero_le i.castSucc)
    exact hnonneg.trans_lt (hr i).1
  · intro i
    have heq : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    exact ⟨by simpa [t, t₀, heq] using (hr i.castSucc).2,
      by simpa [t, t₀] using (hr i.succ).1⟩

end OpenMathResearch.AlternatingSignRoots
