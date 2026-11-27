import ExactCycleProbabilityLimit
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances.CycleProbability
open Filter
open scoped Topology

private def tailBudget (j : ℕ) : ℝ := ((j:ℝ)+1)/(2*(j:ℝ)*j.factorial)

private theorem budget_step {j : ℕ} (hj : 2 ≤ j) :
    1/(2*(j.factorial:ℝ))+tailBudget (j+1) ≤ tailBudget j := by
  have hp : 0 < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hf : 0 < (j.factorial:ℝ) := by positivity
  simp only [tailBudget,Nat.factorial_succ,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
  apply sub_nonneg.mp
  have he : ((j:ℝ)+1)/(2*j*j.factorial) -
      (1/(2*(j.factorial:ℝ))+((j:ℝ)+1+1)/(2*((j:ℝ)+1)*(((j:ℝ)+1)*j.factorial))) =
      1/(2*(j:ℝ)*((j:ℝ)+1)^2*j.factorial) := by
    field_simp [hp.ne',hf.ne',show (j:ℝ)+1 ≠ 0 by positivity] <;> ring
  rw [he]
  positivity

private theorem walk_bound (f : ℕ→ℝ) (a K : ℕ) (B : ℝ)
    (h : ∀ i < K, |f (a+i+1)-f (a+i)| ≤ B) :
    |f (a+K)-f a| ≤ K*B := by
  have hh (t : ℕ) (ht : t ≤ K) : |f (a+t)-f a| ≤ t*B := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hx := abs_sub_le (f (a+t+1)) (f (a+t)) (f a)
      have hy := ih (by omega)
      have hz := h t (by omega)
      rw [Nat.cast_succ]
      change |f (a+t+1)-f a| ≤ _
      linarith
  exact hh K le_rfl

private theorem clamped_block {k j N : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 0 < k)
    (hj : 2 ≤ j) :
    (k:ℝ)*|d (max ((j+1)*k) N)-d (max (j*k) N)| ≤ 1/(2*(j.factorial:ℝ)) := by
  let f (s:ℕ) := d (max s N)
  let B : ℝ := 1/(2*(j.factorial:ℝ)*(k:ℝ)^2)
  have hh : ∀ i < k, |f (j*k+i+1)-f (j*k+i)| ≤ B := by
    intro i hi
    by_cases hs : N ≤ j*k+i
    · have hx := hd.numeratorDiff_factorial_block hk hj
          (show j*k < j*k+i+1 by omega) (show j*k+i+1 ≤ (j+1)*k by rw [Nat.add_mul]; omega)
      have hklo : k ≤ j*k+i := by nlinarith
      simpa [f,max_eq_left hs,max_eq_left (by omega : N ≤ j*k+i+1),numeratorDiff,
        cutoffWeight,show k ≤ j*k+i+1 by omega,hklo,B] using hx
    · simp [f,max_eq_right (by omega : j*k+i+1 ≤ N),max_eq_right (by omega : j*k+i ≤ N),B]
      positivity
  have hw := mul_le_mul_of_nonneg_left (walk_bound f (j*k) k B hh) (by positivity : 0 ≤ (k:ℝ))
  have hx : (k:ℝ)*((k:ℝ)*B)=1/(2*(j.factorial:ℝ)) := by
    dsimp [B]
    field_simp <;> ring
  rw [hx] at hw
  simpa only [f,Nat.add_mul,Nat.one_mul] using hw

/-- The full factorial tail on the original probability, valid inside a block. -/
theorem probability_factorial_tail {m j N : ℕ} {d : ℕ→ℝ} (hd : Spec (m+1) d)
    (hj : 2 ≤ j) (hN : j*(m+1) ≤ N) :
    (m+1:ℝ)*|Real.exp (-cycleHarmonic m)-d N| ≤ ((j:ℝ)+1)/(2*(j:ℝ)*j.factorial) := by
  let k := m+1
  have hk : 0 < k := by dsimp [k]; omega
  let v (t : ℕ) := max ((j+t)*k) N
  have hwalk (t : ℕ) : (k:ℝ)*|d (v t)-d N| + tailBudget (j+t) ≤ tailBudget j := by
    induction t with
    | zero => simp [v, max_eq_right hN,k]
    | succ t ih =>
      have hstep := clamped_block (N:=N) hd hk (show 2 ≤ j+t by omega)
      have hb := budget_step (show 2 ≤ j+t by omega)
      have htri := mul_le_mul_of_nonneg_left (abs_sub_le (d (v (t+1))) (d (v t)) (d N))
        (by positivity : 0 ≤ (k:ℝ))
      change (k:ℝ)*|d (v (t+1))-d (v t)| ≤ _ at hstep
      change (k:ℝ)*|d (v (t+1))-d N| + tailBudget ((j+t)+1) ≤ _
      linarith
  have hv : Tendsto v atTop atTop := by
    apply tendsto_atTop_mono (f:=fun t : ℕ => t) _ tendsto_id
    intro t
    exact le_trans (by dsimp [k]; nlinarith : t ≤ (j+t)*k) (le_max_left _ _)
  have hlim := (((probability_tends_to_harmonic m hd).comp hv).sub_const (d N)).abs.const_mul (k:ℝ)
  have hfinal := le_of_tendsto hlim (Eventually.of_forall (fun t => show
      (k:ℝ)*|d (v t)-d N| ≤ tailBudget j by
        have hp : 0 ≤ tailBudget (j+t) := by unfold tailBudget; positivity
        linarith only [hwalk t,hp]))
  simpa [k,tailBudget] using hfinal

#print axioms probability_factorial_tail
end OpenMathResearch.LongCycleExcedances.CycleProbability
