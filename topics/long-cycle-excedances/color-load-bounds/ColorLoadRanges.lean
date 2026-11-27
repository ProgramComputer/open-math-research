import MarkedLoadProbability
import LoadEnvelope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.ColorAnchor
open Finset Real
open scoped Classical

private theorem bounded_subtype_sum (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (F : ℕ → ℝ) : (∑ i : {a : Fin N // P a.val}, F i.val.val) =
    ∑ i ∈ (range N).filter P, F i := by
  rw [←Finset.sum_subtype ((univ : Finset (Fin N)).filter (fun i => P i.val)) (by simp) (fun i => F i.val)]
  rw [sum_filter,sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if P i then F i else 0) N

/-- Separate the finite ranges of marked orbit lengths and binomial loads. -/
theorem expected_color_marks_product (n p : ℕ) (S T : ℕ → Prop) :
    expectedColorMarks n p (fun j i => S j ∧ T i) =
      ∑ j ∈ (range (p+1)).filter (fun j => 0 < j ∧ S j),
      (∑ i ∈ (range (n+1)).filter T, colorLoad n i ((j:ℝ)/p))/(j:ℝ) := by
  classical
  unfold expectedColorMarks
  let G (j : ℕ) := ∑ i : {i : Fin (n+1) // S j ∧ T i.val}, colorLoad n i.val.val ((j:ℝ)/p)/(j:ℝ)
  trans ∑ j ∈ (range (p+1)).filter (fun j => 0 < j), G j
  · convert bounded_subtype_sum (p+1) (fun j => 0 < j) G using 1
    congr! 6
  dsimp only [G]
  rw [sum_filter,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h0 : 0 < j
  · rw [if_pos h0]
    trans ∑ i ∈ (range (n+1)).filter (fun i => S j ∧ T i), colorLoad n i ((j:ℝ)/p)/(j:ℝ)
    · convert bounded_subtype_sum (n+1) (fun i => S j ∧ T i) (fun i => colorLoad n i ((j:ℝ)/p)/(j:ℝ)) using 1
    by_cases hS : S j
    · simp only [h0,hS,true_and,if_true,sum_div]
    · simp [hS]
  · simp [h0]

/-- At most b-1 small sizes can contribute to the upper comparison. -/
theorem color_short_load_budget (n p k b : ℕ) (hp : 0 < p)
    (hmean : ∀ j, 0 < j → j < b → j≤p → (n:ℝ)*((j:ℝ)/p) ≤ 2*(k:ℝ)/3) :
    expectedColorMarks n p (fun j i => j < b ∧ k ≤ i) ≤
      ((b-1:ℕ):ℝ)*exp (-(k:ℝ)/15) := by
  rw [expected_color_marks_product]
  let s := (range (p+1)).filter (fun j => 0 < j ∧ j < b)
  have hpoint (j : ℕ) (hj : j∈s) :
      (∑ i ∈ (range (n+1)).filter (k ≤ ·), colorLoad n i ((j:ℝ)/p))/(j:ℝ) ≤ exp (-(k:ℝ)/15) := by
    obtain ⟨hjp,hj0,hjb⟩ := mem_filter.mp hj
    have hjp' : j≤p := Nat.lt_succ_iff.mp (mem_range.mp hjp)
    have htail := color_load_upper_tail n k (x:=(j:ℝ)/p) (by positivity)
      ((div_le_one (by positivity)).2 (by exact_mod_cast hjp')) (hmean j hj0 hjb hjp')
    apply (div_le_iff₀ (by positivity : (0:ℝ) < j)).2
    exact htail.trans (le_mul_of_one_le_right (exp_pos _).le (by exact_mod_cast hj0))
  have hsize : s.card≤b-1 := by
    have hh : s ⊆ Ico 1 b := fun j hj => mem_Ico.mpr (mem_filter.mp hj).2
    simpa only [Nat.card_Ico] using card_le_card hh
  have hcast : (s.card:ℝ)≤((b-1:ℕ):ℝ) := by exact_mod_cast hsize
  calc
    _ ≤ ∑ _j ∈ s, exp (-(k:ℝ)/15) := by convert sum_le_sum hpoint using 1; congr! 5
    _ = (s.card:ℝ)*exp (-(k:ℝ)/15) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcast (exp_pos _).le

/-- The lower comparison requires one geometric series over marked orbit
lengths. The factor 1/b comes from the exact 1/j first moment. -/
theorem color_long_load_budget (n p k b : ℕ) (hp : 0 < p) (hn : 0 < n) (hb : 0 < b)
    (hmean : ∀ j, b ≤ j → j ≤ p → (k:ℝ) ≤ 3*(n:ℝ)*((j:ℝ)/p)/4) :
    let r := exp (-(n:ℝ)/(32*(p:ℝ)))
    expectedColorMarks n p (fun j i => b ≤ j ∧ i < k) ≤ (1/b)*(r/(1-r)) := by
  dsimp only
  rw [expected_color_marks_product]
  let r := exp (-(n:ℝ)/(32*(p:ℝ)))
  have hr : 0 < r := exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) (by positivity))
  let s := (range (p+1)).filter (fun j => 0 < j ∧ b≤j)
  let U (j : ℕ) : ℝ := if j=0 then 0 else (1/b)*r^j
  have hjj (j : ℕ) (hj : j∈s) :
      (∑ i ∈ (range (n+1)).filter (· < k), colorLoad n i ((j:ℝ)/p))/(j:ℝ) ≤ U j := by
    obtain ⟨hjp,hj0,hbj⟩ := mem_filter.mp hj
    have hjp' : j≤p := Nat.lt_succ_iff.mp (mem_range.mp hjp)
    have he := color_load_lower_tail n k (x:=(j:ℝ)/p) (by positivity)
      ((div_le_one (by positivity)).2 (by exact_mod_cast hjp')) (hmean j hbj hjp')
    have hpow : exp (-(n:ℝ)*((j:ℝ)/p)/32) = r^j := by
      dsimp [r]; rw [←exp_nat_mul]; congr 1; ring
    rw [hpow] at he
    simp only [U,if_neg hj0.ne']
    calc
      _ ≤ r^j/(j:ℝ) := div_le_div_of_nonneg_right he (by positivity)
      _ ≤ r^j/(b:ℝ) := div_le_div_of_nonneg_left (pow_nonneg hr.le _) (by positivity) (by exact_mod_cast hbj)
      _ = _ := by ring
  have hsum : (∑ j ∈ range (p+1), U j) = (1/b)*r*(∑ i ∈ range p, r^i) := by
    rw [sum_range_succ']; simp only [U,Nat.succ_ne_zero,if_false,if_true,add_zero]
    rw [mul_sum]; apply sum_congr rfl
    intro i _; rw [pow_succ]; ring
  have hg := geom_sum_mul r p
  have hge : (1-r)*(∑ i ∈ range p, r^i) ≤ 1 := by nlinarith [pow_nonneg hr.le p]
  have hfin : (∑ i ∈ range p, r^i) ≤ 1/(1-r) := (le_div_iff₀ (sub_pos.mpr hr1)).2 (by linarith)
  calc
    _ ≤ ∑ j ∈ s, U j := by convert sum_le_sum hjj using 1; congr! 5
    _ ≤ ∑ j ∈ range (p+1), U j := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ => by
      dsimp [U]; split <;> positivity)
    _ = _ := hsum
    _ ≤ (1/b)*r*(1/(1-r)) := mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = _ := by ring

#print axioms color_long_load_budget
#print axioms expected_color_marks_product
#print axioms color_short_load_budget
end OpenMathResearch.LongCycleExcedances.ColorAnchor
