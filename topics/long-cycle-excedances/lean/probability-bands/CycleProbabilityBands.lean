import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances.CycleProbability

open Finset

structure Spec (k : ℕ) (d : ℕ → ℝ) : Prop where
  zero : d 0 = 1
  small : ∀ r, 0 < r → r < k → d r = 0
  recurrence : ∀ r, k ≤ r → (r : ℝ) * d r = ∑ j ∈ range (r-k+1), d j

private theorem sum_early {k : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ k) : ∑ j ∈ range m, d j = 1 := by
  rw [sum_eq_single 0, h.zero]
  · intro i hi hne
    exact h.small i (Nat.pos_of_ne_zero hne) (lt_of_lt_of_le (mem_range.mp hi) hmk)
  · simp [hm]

theorem one_cycle {k : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    {r : ℕ} (hr : k ≤ r) (hu : r < 2*k) :
    d r = 1 / (r : ℝ) := by
  have he := h.recurrence r hr
  rw [sum_early h (by omega) (by omega)] at he
  have hp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply (eq_div_iff hp.ne').2
  simpa [mul_comm] using he

theorem adjacent {k : ℕ} {d : ℕ → ℝ} (h : Spec k d)
    {r : ℕ} (hr : k < r) : (r : ℝ) * d r = (↑(r-1) : ℝ) * d (r-1) + d (r-k) := by
  have he := h.recurrence r (by omega)
  have hl := h.recurrence (r-1) (by omega)
  have len : r-k+1 = (r-1-k+1)+1 := by omega
  have ix : r-1-k+1 = r-k := by omega
  rw [len, sum_range_succ, ← hl, ix] at he
  exact he

theorem propagate_upper {k l : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k)
    (hl : k ≤ l) (B : ℝ) (seed : ∀ r, l ≤ r → r < l+k → (k : ℝ)*d r ≤ B) :
    ∀ r, l ≤ r → (k : ℝ)*d r ≤ B := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hs : r < l+k
    · exact seed r hr hs
    have hc : (r : ℝ) = (↑(r-1) : ℝ)+1 := by
      exact_mod_cast (show r = (r-1)+1 by omega)
    have kp : (0 : ℝ) ≤ k := by positivity
    have rp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hn : (0 : ℝ) ≤ (r-1 : ℕ) := by positivity
    have hp := ih (r-1) (by omega) (by omega)
    have hq := ih (r-k) (by omega) (by omega)
    apply le_of_not_gt
    intro bad
    apply (not_lt_of_ge ?_) (mul_lt_mul_of_pos_left bad rp)
    calc
      (r : ℝ) * ((k : ℝ)*d r) =
          (↑(r-1) : ℝ) * ((k : ℝ)*d (r-1)) + (k : ℝ)*d (r-k) := by
        calc
          _ = (k : ℝ) * ((r : ℝ)*d r) := by ring
          _ = _ := by rw [adjacent h (by omega)]; ring
      _ ≤ (↑(r-1) : ℝ) * B + B := add_le_add (mul_le_mul_of_nonneg_left hp hn) hq
      _ = (r : ℝ) * B := by rw [hc]; ring

theorem propagate_lower {k l : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k)
    (hl : k ≤ l) (B : ℝ) (seed : ∀ r, l ≤ r → r < l+k → B < (k : ℝ)*d r) :
    ∀ r, l ≤ r → B < (k : ℝ)*d r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hs : r < l+k
    · exact seed r hr hs
    have hc : (r : ℝ) = (↑(r-1) : ℝ)+1 := by
      exact_mod_cast (show r = (r-1)+1 by omega)
    have rp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hn : (0 : ℝ) ≤ (r-1 : ℕ) := by positivity
    have hp := ih (r-1) (by omega) (by omega)
    have hq := ih (r-k) (by omega) (by omega)
    apply lt_of_not_ge
    intro bad
    apply (not_lt_of_ge (mul_le_mul_of_nonneg_left bad rp.le))
    calc
      (r : ℝ) * B = (↑(r-1) : ℝ) * B + B := by rw [hc]; ring
      _ < (↑(r-1) : ℝ) * ((k : ℝ)*d (r-1)) + (k : ℝ)*d (r-k) :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hp.le hn) hq
      _ = (r : ℝ) * ((k : ℝ)*d r) := by
        calc
          _ = (k : ℝ) * ((↑(r-1) : ℝ)*d (r-1) + d (r-k)) := by ring
          _ = _ := by rw [← adjacent h (by omega)]; ring

theorem lower_half {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) :
    ∀ r, k ≤ r → (1/2 : ℝ) < (k : ℝ)*d r := by
  apply propagate_lower h hk le_rfl
  intro r hr hu
  rw [one_cycle h hr (by omega)]
  have rp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h2 : (r : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (show r < 2*k by omega)
  rw [mul_one_div, lt_div_iff₀ rp]
  linarith


private theorem log_step_upper {x : ℝ} (hx : 0 < x) :
    Real.log (x+1) - Real.log x ≤ 1/x := by
  have hy : 0 < x+1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have e : (x+1)/x-1=1/x := by field_simp <;> ring
  linarith

private theorem log_step_lower {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1) - Real.log x := by
  have hy : 0 < x+1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have e : x/(x+1)-1= -(1/(x+1)) := by field_simp <;> ring
  linarith

private theorem harmonic_left {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.log (x+(m : ℝ)) - Real.log x ≤ ∑ i ∈ range m, 1/(x+(i : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ, ← add_assoc]
    have hp := log_step_upper (x := x+(m : ℝ)) (by positivity)
    linarith

private theorem harmonic_upper {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (∑ i ∈ range (m+1), 1/(x+(i : ℝ))) ≤ 1/x + Real.log (x+(m : ℝ)) - Real.log x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ, ← add_assoc]
    have hp := log_step_lower (x := x+(m : ℝ)) (by positivity)
    linarith

private theorem second_block_equation {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k)
    (m : ℕ) (hm : m < k) :
    (↑(2*k+m) : ℝ) * d (2*k+m) =
      1 + ∑ i ∈ range (m+1), 1/((k : ℝ)+(i : ℝ)) := by
  have he := h.recurrence (2*k+m) (by omega)
  have ix : 2*k+m-k+1 = k+(m+1) := by omega
  rw [ix, sum_range_add, sum_early h hk le_rfl] at he
  rw [he]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [one_cycle h (by omega) (by have := mem_range.mp hi; omega), Nat.cast_add]

theorem upper_of_tangent {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k)
    {B : ℝ} (hB : 0 < B) (scalar : 1/(k : ℝ)+Real.log (1/B) ≤ B) :
    ∀ r, 2*k ≤ r → (k : ℝ)*d r ≤ B := by
  apply propagate_upper h hk (by omega)
  intro r hr hu
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hm : m < k := by omega
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  let y : ℝ := ((k : ℝ)+(m : ℝ))/(k : ℝ)
  have yp : 0 < y := div_pos (by positivity) kp
  have lg := Real.log_le_sub_one_of_pos (mul_pos hB yp)
  rw [Real.log_mul hB.ne' yp.ne'] at lg
  have invlog : Real.log (1/B) = -Real.log B := by rw [one_div, Real.log_inv]
  have hh := harmonic_upper kp m
  have eld : Real.log y = Real.log ((k : ℝ)+(m : ℝ)) - Real.log (k : ℝ) :=
    Real.log_div (by positivity) kp.ne'
  have he := second_block_equation h hk m hm
  have yp' : 0 < 1+y := by linarith
  apply le_of_not_gt
  intro bad
  apply (not_lt_of_ge ?_) (mul_lt_mul_of_pos_left bad yp')
  calc
    (1+y)*((k : ℝ)*d (2*k+m)) = (↑(2*k+m) : ℝ)*d (2*k+m) := by
      dsimp [y]
      push_cast
      field_simp <;> ring
    _ = _ := he
    _ ≤ B * (1+y) := by rw [eld] at lg; rw [invlog] at scalar; linarith
    _ = (1+y)*B := by ring

private theorem log_scalar {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (check : x ≤ ∑ i ∈ range 6, y^i/(i.factorial : ℝ)) : Real.log x ≤ y :=
  (Real.log_le_iff_le_exp hx).2 (check.trans (Real.sum_le_exp_of_nonneg hy 6))

private theorem scalar61 : Real.log (1/(61/100 : ℝ)) ≤ 61/100-1/13 := by
  apply log_scalar (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem scalar59 : Real.log (1/(59/100 : ℝ)) ≤ 59/100-1/22 := by
  apply log_scalar (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem scalar47 : Real.log (1/(4/7 : ℝ)) ≤ 4/7-1/100 := by
  apply log_scalar (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem upper_fixed {K k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hK : 0 < K)
    (hk : K ≤ k) {B : ℝ} (hB : 0 < B) (hs : Real.log (1/B) ≤ B - 1/(K : ℝ)) :
    ∀ r, 2*k ≤ r → (k : ℝ)*d r ≤ B := by
  have kp : 0 < k := by omega
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hsmall := one_div_le_one_div_of_le hK' hk'
  exact upper_of_tangent h kp hB (by linarith)

theorem upper61 {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 13 ≤ k) :
    ∀ r, 2*k ≤ r → (k : ℝ)*d r ≤ 61/100 :=
  upper_fixed h (by decide) hk (by norm_num) scalar61

theorem upper59 {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 22 ≤ k) :
    ∀ r, 2*k ≤ r → (k : ℝ)*d r ≤ 59/100 :=
  upper_fixed h (by decide) hk (by norm_num) scalar59

theorem upper47 {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 100 ≤ k) :
    ∀ r, 2*k ≤ r → (k : ℝ)*d r ≤ 4/7 :=
  upper_fixed h (by decide) hk (by norm_num) scalar47


private theorem harmonic_two_le {x : ℕ} (hx : 0 < x) :
    Real.log 2 ≤ ∑ i ∈ range x, 1/((x : ℝ)+(i : ℝ)) := by
  have xp : (0 : ℝ) < x := by exact_mod_cast hx
  have h := harmonic_left xp x
  have eq : (x : ℝ) + x = 2 * (x : ℝ) := by ring
  rw [eq, Real.log_mul (by norm_num) xp.ne'] at h
  simpa using h

theorem lower548 {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) :
    ∀ r, 3*k ≤ r → (548/1000 : ℝ) < (k : ℝ)*d r := by
  apply propagate_lower h hk (by omega)
  intro r hr hu
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hm : m < k := by omega
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  have mc : (m : ℝ) < (k : ℝ) := by exact_mod_cast hm
  have he := h.recurrence (3*k+m) (by omega)
  have ix : 3*k+m-k+1 = (k+k)+(m+1) := by omega
  rw [ix, sum_range_add, sum_range_add, sum_early h hk le_rfl] at he
  have eqFirst : (∑ i ∈ range k, d (k+i)) =
      ∑ i ∈ range k, 1/((k : ℝ)+(i : ℝ)) := by
    apply sum_congr rfl
    intro i hi
    rw [one_cycle h (by omega) (by have := mem_range.mp hi; omega), Nat.cast_add]
  rw [eqFirst] at he
  have hed : (∑ i ∈ range (m+1), 1/(2*(k : ℝ))) ≤
      ∑ i ∈ range (m+1), d ((k+k)+i) := by
    apply sum_le_sum
    intro i hi
    apply (div_le_iff₀ (by positivity : 0 < 2*(k : ℝ))).2
    have hl := lower_half h hk ((k+k)+i) (by omega)
    nlinarith
  have hmid : Real.log 2 ≤ ∑ i ∈ range k, 1/((k : ℝ)+(i : ℝ)) := harmonic_two_le hk
  let y : ℝ := (m : ℝ)/(k : ℝ)
  have hy : y < 1 := (div_lt_one kp).2 mc
  have yp : 0 ≤ y := div_nonneg (by positivity) kp.le
  have z : (∑ i ∈ range (m+1), 1/(2*(k : ℝ))) = y/2 + 1/(2*(k : ℝ)) := by
    dsimp [y]
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_succ]
    field_simp <;> ring
  rw [z] at hed
  have ln2 := Real.log_two_gt_d9
  have nonneg : 0 ≤ 1/(2*(k : ℝ)) := by positivity
  have yp' : 0 < 3+y := by linarith
  apply lt_of_not_ge
  intro bad
  apply (not_lt_of_ge (mul_le_mul_of_nonneg_left bad yp'.le))
  calc
    (3+y)*(548/1000 : ℝ) < (↑(3*k+m) : ℝ)*d (3*k+m) := by linarith
    _ = (3+y)*((k : ℝ)*d (3*k+m)) := by
      dsimp [y]
      push_cast
      field_simp <;> ring


theorem lower547 {k : ℕ} {d : ℕ → ℝ} (h : Spec k d) (hk : 0 < k) (r : ℕ) (hr : 3*k ≤ r) :
    (547/1000 : ℝ) < (k : ℝ)*d r :=
  lt_trans (by norm_num) (lower548 h hk r hr)

/-- Factorial normalization of the exact recurrence obtained by choosing the
support of the cycle through one distinguished label. -/
theorem from_anchored_counts {k : ℕ} (hk : 0 < k) (count : ℕ → ℝ)
    (hzero : count 0 = 1) (hsmall : ∀ r, 0 < r → r < k → count r = 0)
    (hcount : ∀ r, k ≤ r → count r = ∑ a ∈ Icc k r,
      ((r-1).choose (a-1) : ℝ) * ((a-1).factorial : ℝ) * count (r-a)) :
    Spec k (fun r => count r / (r.factorial : ℝ)) := by
  refine ⟨by simp [hzero], ?_, ?_⟩
  · intro r hp hs
    simp [hsmall r hp hs]
  · intro r hr
    have pr : 0 < r := by omega
    have pr' : (r : ℝ) ≠ 0 := by exact_mod_cast pr.ne'
    have pf : (↑(r-1).factorial : ℝ) ≠ 0 := by positivity
    have fact : (r.factorial : ℝ) = (r : ℝ) * (↑(r-1).factorial : ℝ) := by
      exact_mod_cast (show r.factorial = r * (r-1).factorial by
        have he := Nat.factorial_succ (r-1)
        rwa [show r-1+1=r by omega] at he)
    change (r : ℝ)*(count r/(r.factorial : ℝ)) =
      ∑ j ∈ range (r-k+1), count j/(j.factorial : ℝ)
    calc
      (r : ℝ)*(count r/(r.factorial : ℝ)) = count r/(↑(r-1).factorial : ℝ) := by
        rw [fact]
        field_simp <;> ring
      _ = ∑ a ∈ Icc k r, count (r-a)/((r-a).factorial : ℝ) := by
        rw [hcount r hr, div_eq_mul_inv, sum_mul]
        apply sum_congr rfl
        intro a ha
        have hra := (mem_Icc.mp ha).2
        have hka := (mem_Icc.mp ha).1
        have f := Nat.choose_mul_factorial_mul_factorial (show a-1 ≤ r-1 by omega)
        rw [show r-1-(a-1)=r-a by omega] at f
        have f' : ((r-1).choose (a-1) : ℝ) * ((a-1).factorial : ℝ) *
            ((r-a).factorial : ℝ) = ((r-1).factorial : ℝ) := by exact_mod_cast f
        have q : (↑(r-a).factorial : ℝ) ≠ 0 := by positivity
        rw [← div_eq_mul_inv]
        apply (div_eq_div_iff pf q).2
        rw [← f']
        ring
      _ = ∑ j ∈ range (r-k+1), count j/(j.factorial : ℝ) := by
        apply sum_bij (fun a _ => r-a)
        · intro a ha
          have := mem_Icc.mp ha
          exact mem_range.mpr (by omega)
        · intro a ha b hb he
          have := (mem_Icc.mp ha).2
          have := (mem_Icc.mp hb).2
          omega
        · intro j hj
          have := mem_range.mp hj
          exact ⟨r-j, mem_Icc.mpr (by omega), by omega⟩
        · intro a ha
          rfl

#print axioms from_anchored_counts
#print axioms upper61
#print axioms upper59
#print axioms upper47
#print axioms lower547
#print axioms lower548
end OpenMathResearch.LongCycleExcedances.CycleProbability
