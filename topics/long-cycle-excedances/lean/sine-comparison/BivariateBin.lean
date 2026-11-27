import BinProductMajorant
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

def degreeBin (k s : ℕ) : ℕ := (4*s+k-1)/k

def markDegreeBin (k N : ℕ) (c : ℕ → ℝ) : ℝ[X][X] :=
  ∑ s ∈ Icc k N, monomial (degreeBin k s) (monomial s (c s))

def forgetDegree (P : ℝ[X][X]) : ℝ[X] := P.map (evalRingHom 1)

def markedMultiple {ι : Type*} (A : Finset ι) (P : ι → ℝ[X][X]) : ℝ[X][X] :=
  ∑ T ∈ A.powerset.filter (fun T => 2 ≤ T.card), ∏ q ∈ T, P q

private def NN (P : ℝ[X][X]) : Prop := ∀ b d, 0 ≤ (P.coeff b).coeff d
private theorem nn_add {P Q : ℝ[X][X]} (hP : NN P) (hQ : NN Q) : NN (P+Q) := by
  intro b d
  simp only [coeff_add]
  exact add_nonneg (hP b d) (hQ b d)
private theorem nn_mul {P Q : ℝ[X][X]} (hP : NN P) (hQ : NN Q) : NN (P*Q) := by
  intro b d
  simp only [coeff_mul, finsetSum_coeff]
  exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => mul_nonneg (hP i.1 j.1) (hQ i.2 j.2)))
private theorem nn_sum {ι : Type*} (A : Finset ι) (P : ι → ℝ[X][X])
    (h : ∀ q ∈ A, NN (P q)) : NN (∑ q ∈ A, P q) := by
  intro b d
  simp only [finsetSum_coeff]
  exact sum_nonneg (fun i hi => h i hi b d)
private theorem nn_prod {ι : Type*} (A : Finset ι) (P : ι → ℝ[X][X])
    (h : ∀ q ∈ A, NN (P q)) : NN (∏ q ∈ A, P q) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro b d
    by_cases hb : b=0 <;> by_cases hd : d=0 <;> simp [coeff_one,hb,hd]
  | @insert q A hq ih =>
    rw [prod_insert hq]
    exact nn_mul (h q (mem_insert_self ..)) (ih fun i hi => h i (mem_insert_of_mem hi))
private theorem nn_mark (k N : ℕ) (c : ℕ → ℝ) (h : ∀ s, 0 ≤ c s) :
    NN (markDegreeBin k N c) := by
  apply nn_sum
  intro s _ b d
  rw [coeff_monomial]
  split
  · rw [coeff_monomial]
    split
    · exact h s
    · norm_num
  · simp

theorem coeff_markDegreeBin {k N b d : ℕ} (c : ℕ → ℝ) :
    ((markDegreeBin k N c).coeff b).coeff d =
      if d ∈ Icc k N ∧ degreeBin k d=b then c d else 0 := by
  classical
  rw [markDegreeBin, finsetSum_coeff, finsetSum_coeff]
  by_cases hd : d ∈ Icc k N
  · rw [sum_eq_single_of_mem d hd]
    · by_cases hb : degreeBin k d=b <;> simp [coeff_monomial, hd,hb]
    · intro s _ hs
      by_cases hb : degreeBin k s=b <;> simp [coeff_monomial,hb,hs]
  · rw [sum_eq_zero]
    · simp [hd]
    · intro s hs
      have hsd : s ≠ d := fun he => hd (he ▸ hs)
      by_cases hb : degreeBin k s=b <;> simp [coeff_monomial,hb,hsd]

theorem coeff_le_forgetDegree {P : ℝ[X][X]} (hP : NN P) (b d : ℕ) :
    (P.coeff b).coeff d ≤ (forgetDegree P).coeff b := by
  rw [forgetDegree, coeff_map]
  change (P.coeff b).coeff d ≤ (P.coeff b).eval 1
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hd : d ≤ (P.coeff b).natDegree
  · exact single_le_sum (fun j _ => hP b j) (mem_range.mpr (Nat.lt_succ_of_le hd))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hd)]
    exact sum_nonneg (fun j _ => hP b j)

/-- The finite sum over configurations with two or more occupied indices
is exactly the full polynomial less its empty and one-index parts. -/
theorem markedMultiple_eq {ι : Type*} (A : Finset ι) (P : ι → ℝ[X][X]) :
    markedMultiple A P = (∏ q ∈ A, (1+P q))-1-∑ q ∈ A, P q := by
  classical
  let g := fun T : Finset ι => ∏ q ∈ T, P q
  have hpartition := sum_filter_add_sum_filter_not A.powerset (fun T => 2 ≤ T.card) g
  have hsmall : A.powerset.filter (fun T => ¬2 ≤ T.card) =
      insert ∅ (A.image fun q => ({q}:Finset ι)) := by
    ext T
    simp only [mem_filter,mem_powerset,mem_insert,mem_image]
    constructor
    · rintro ⟨ht,hcard⟩
      by_cases he : T = ∅
      · exact Or.inl he
      · have hT : T.card=1 := by
          have := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
          omega
        obtain ⟨q,rfl⟩ := card_eq_one.mp hT
        exact Or.inr ⟨q,ht (mem_singleton_self q),rfl⟩
    · rintro (rfl|⟨q,hq,rfl⟩)
      · simp
      · simp [hq]
  rw [hsmall, sum_insert (by simp), sum_image] at hpartition
  · simp only [g,prod_empty,prod_singleton] at hpartition
    rw [prod_one_add]
    unfold markedMultiple
    rw [← hpartition]
    ring
  · intro q _ r _ he
    simpa using he

theorem forgetDegree_markedMultiple {ι : Type*} (A : Finset ι) (P : ι → ℝ[X][X]) :
    forgetDegree (markedMultiple A P) = binMultiple A (fun q => forgetDegree (P q)) := by
  rw [markedMultiple_eq,binMultiple,binFull,binLinear]
  change (mapRingHom (evalRingHom 1)) ((∏ q ∈ A, (1+P q))-1-∑ q ∈ A, P q) = _
  simp only [map_sub,map_prod,map_sum,map_add,map_one]
  rfl

theorem marked_bin_bounds {ι : Type*} (A : Finset ι) (k N : ℕ)
    (c : ι → ℕ → ℝ) (hc : ∀ q ∈ A, ∀ s, 0 ≤ c q s) (b d : ℕ) :
    let P := fun q => markDegreeBin k N (c q)
    let p := fun q => forgetDegree (P q)
    (((∏ q ∈ A, (1+P q)).coeff b).coeff d ≤ (binFull A p).coeff b) ∧
      (((markedMultiple A P).coeff b).coeff d ≤ (binMultiple A p).coeff b) := by
  classical
  dsimp only
  let P := fun q => markDegreeBin k N (c q)
  have hp (q : ι) (hq : q ∈ A) : NN (P q) := nn_mark _ _ _ (hc q hq)
  have h1 : NN (1:ℝ[X][X]) := by
    intro i j
    by_cases hi : i=0 <;> simp [coeff_one,hi]
    split <;> norm_num
  constructor
  · have hh := coeff_le_forgetDegree (nn_prod A (fun q => 1+P q)
      (fun q hq => nn_add h1 (hp q hq))) b d
    have he : forgetDegree (∏ q ∈ A, (1+P q)) = binFull A (fun q => forgetDegree (P q)) := by
      change (mapRingHom (evalRingHom 1)) (∏ q ∈ A, (1+P q)) = _
      simp [binFull,forgetDegree]
    simpa only [he] using hh
  · have hM : NN (markedMultiple A P) := by
      apply nn_sum
      intro T hT
      exact nn_prod T P (fun q hq => hp q ((mem_powerset.mp (mem_filter.mp hT).1) hq))
    simpa only [forgetDegree_markedMultiple] using coeff_le_forgetDegree hM b d

/-- Nonnegativity of every joint bin/degree of the full marked product. -/
theorem marked_full_nonnegative {ι : Type*} (A : Finset ι) (k N : ℕ)
    (c : ι → ℕ→ℝ) (hc : ∀ q ∈ A, ∀ d, 0 ≤ c q d) :
    ∀ b d, 0 ≤ ((∏ q ∈ A, (1+markDegreeBin k N (c q))).coeff b).coeff d := by
  classical
  have hone : NN (1:ℝ[X][X]) := by
    intro b d
    by_cases h : b=0 <;> simp [coeff_one,h]
    split <;> norm_num
  exact nn_prod A _ (fun q hq => nn_add hone (nn_mark k N _ (hc q hq)))
#print axioms marked_full_nonnegative

#print axioms markedMultiple_eq
#print axioms marked_bin_bounds
#print axioms coeff_markDegreeBin
#print axioms coeff_le_forgetDegree
end OpenMathResearch.LongCycleExcedances
