import LongCycleBounds.GeneralCycleSupports
import LongCycleBounds.PoleBridge

noncomputable section
namespace RepositoryQuotientAudit
open Finset LongCycleBounds LongCycleBounds.Band LongCycleBounds.CycleCount
open LongCycleBounds.PoleBridge LongCycleBounds.PoleTails LongCycleBounds.Bulk

theorem orderedMomentRow_congr_on_support {M A : ℕ → ℝ} {k : ℕ} (hEq : ∀ a ≥ k, M a = A a)
    (n h : ℕ) : orderedMomentRow M n k h = orderedMomentRow A n k h := by
  induction h generalizing n with
  | zero => simp [orderedMomentRow]
  | succ h ih =>
    rw [orderedMomentRow, orderedMomentRow]
    apply sum_congr rfl
    intro a ha
    rw [hEq a (mem_Icc.mp ha).1, ih]

/-- Error propagation for replacing each cycle factor by a bounded approximation. -/
theorem orderedMomentRow_approximation {M A F : ℕ → ℝ} {k : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (hf : ∀ a ≥ k, 0 ≤ F a) (ha : ∀ a ≥ k, |A a| ≤ F a)
    (hd : ∀ a ≥ k, |M a - A a| ≤ ε * F a)
    (n h : ℕ) :
    |orderedMomentRow M n k h| ≤ (1+ε)^h * orderedMomentRow F n k h ∧
      |orderedMomentRow M n k h - orderedMomentRow A n k h| ≤ ((1+ε)^h-1) * orderedMomentRow F n k h := by
  have hm (a : ℕ) (hak : k ≤ a) : |M a| ≤ (1+ε)*F a := by
    calc
      |M a| = |(M a - A a) + A a| := by ring_nf
      _ ≤ |M a - A a| + |A a| := abs_add_le ..
      _ ≤ ε*F a + F a := add_le_add (hd a hak) (ha a hak)
      _ = _ := by ring
  induction h generalizing n with
  | zero =>
    by_cases hn : n = 0 <;> simp [orderedMomentRow, hn]
  | succ h ih =>
    have hp : 0 ≤ (1+ε)^h := by positivity
    simp_rw [orderedMomentRow.eq_2]
    have hb (a : ℕ) (hak : a ∈ Icc k n) :
        |(n.choose a : ℝ) * M a * orderedMomentRow M (n-a) k h| ≤
          (1+ε)^(h+1) * ((n.choose a : ℝ) * F a * orderedMomentRow F (n-a) k h) := by
      have hc : 0 ≤ (n.choose a : ℝ) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      calc
        _ ≤ (n.choose a : ℝ) * ((1+ε)*F a) * ((1+ε)^h * orderedMomentRow F (n-a) k h) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hm a (mem_Icc.mp hak).1) hc)
            (ih (n-a)).1 (abs_nonneg _) (mul_nonneg hc (mul_nonneg (by positivity) (hf a (mem_Icc.mp hak).1)))
        _ = _ := by rw [pow_succ]; ring
    constructor
    · rw [mul_sum]
      exact (abs_sum_le_sum_abs ..).trans (sum_le_sum hb)
    · rw [← sum_sub_distrib, mul_sum]
      apply (abs_sum_le_sum_abs ..).trans
      apply sum_le_sum
      intro a ha'
      have hak := (mem_Icc.mp ha').1
      have hc : 0 ≤ (n.choose a : ℝ) := by positivity
      have hf' := hf a hak
      have heq :
          (n.choose a : ℝ) * M a * orderedMomentRow M (n-a) k h -
              (n.choose a : ℝ) * A a * orderedMomentRow A (n-a) k h =
            (n.choose a : ℝ) * ((M a - A a) * orderedMomentRow M (n-a) k h +
              A a * (orderedMomentRow M (n-a) k h - orderedMomentRow A (n-a) k h)) := by ring
      rw [heq, abs_mul, abs_of_nonneg hc]
      calc
        _ ≤ (n.choose a : ℝ) * (|(M a - A a) * orderedMomentRow M (n-a) k h| +
              |A a * (orderedMomentRow M (n-a) k h - orderedMomentRow A (n-a) k h)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le ..) hc
        _ ≤ (n.choose a : ℝ) *
              (ε * F a * ((1+ε)^h * orderedMomentRow F (n-a) k h) +
                F a * (((1+ε)^h-1) * orderedMomentRow F (n-a) k h)) := by
          simp only [abs_mul]
          apply mul_le_mul_of_nonneg_left _ hc
          exact add_le_add
            (mul_le_mul (hd a hak) (ih (n-a)).1 (abs_nonneg _) (mul_nonneg he hf'))
            (mul_le_mul (ha a hak) (ih (n-a)).2 (abs_nonneg _) hf')
        _ = _ := by rw [pow_succ]; ring

/-- One cycle moment as an infinite odd-pole series. -/
def cyclePoleMoment (x : ℝ) (a : ℕ) : ℝ :=
  ((a-1).factorial : ℝ) * (oddPoleSum a x).re

/-- Literal original-row expansion over all admissible cycle counts.
Each cycle factor is an odd-pole series. -/
theorem original_normalized_pole_profile (n k : ℕ) (hk : 2 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    normalizedEnumerator n k x =
      ∑ h ∈ range (n/k+1), (1/(h.factorial:ℝ))*orderedMomentRow (cyclePoleMoment x) n k h := by
  rw [normalizedEnumerator_ordered_cycle_rows hk]
  apply sum_congr rfl
  intro h _
  congr 1
  apply orderedMomentRow_congr_on_support _ n h
  intro a ha
  have he := congrArg Complex.re (moment_poles a (hk.trans ha) x hx)
  simpa [cyclePoleMoment, cycleMoment, Complex.mul_re] using he

/-- Magnitude scale for a nearest-pair cycle moment. -/
def cycleMomentScale (x : ℝ) (a : ℕ) : ℝ := 2 * ((a-1).factorial : ℝ) / radius x ^ a

/-- The contribution of the nearest conjugate pair in one cycle. -/
def principalCycleMoment (x : ℝ) (a : ℕ) : ℝ :=
  cycleMomentScale x a * (pole (c x) (s x) 1 ^ a).re

/-- Keeping the nearest conjugate pair in each cycle independently. -/
def principalPoleProfile (n k : ℕ) (x : ℝ) : ℝ :=
  ∑ h ∈ range (n/k+1), (1/(h.factorial:ℝ)) *
    orderedMomentRow (principalCycleMoment x) n k h

def nonprincipalProfileRemainder (n k : ℕ) (x : ℝ) : ℝ :=
  normalizedEnumerator n k x - principalPoleProfile n k x

private theorem pole_tail_bound (x : ℝ) (a : ℕ) (ha : 8 ≤ a)
    (hs : 1 ≤ (a:ℝ) * s x^2) : ‖tail (c x) (s x) a‖ ≤ 1/9 := by
  let p (j : ℕ) : ℝ := 2*(j:ℝ)+5
  let major (j : ℕ) : ℝ := p j * envelope (p j)^4
  have hpos (j : ℕ) : 3 ≤ p j := by
    dsimp [p]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hmajor (j : ℕ) : 0 ≤ major j := by dsimp [major]; positivity
  have hpartial (m : ℕ) : ∑ j ∈ range m, major j ≤ 2/27 := by
    simpa only [major, p] using (two_tails m).1
  have hsum : Summable major := summable_of_sum_range_le hmajor hpartial
  have htotal : ∑' j, major j ≤ 2/27 := Real.tsum_le_of_sum_range_le hmajor hpartial
  have hscale : (8:ℝ) ≤ a := by exact_mod_cast ha
  have est (l : ℝ) (hl : 1 ≤ l) : ‖pole (c x) (s x) l ^ a‖ ≤ envelope l ^ 4 := by
    rw [norm_pole_pow _ _ _ (circle x) hl]
    exact decay_p _ _ _ hl hscale hs
  have hdom (j : ℕ) : ‖pole (c x) (s x) (p j) ^ a‖ ≤ major j * (1/3) := by
    refine (est _ ((by norm_num : (1:ℝ) ≤ 3).trans (hpos j))).trans ?_
    dsimp [major]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hpos j)) (show 0 ≤ envelope (p j)^4 by positivity)]
  have hf : Summable (fun j => ‖pole (c x) (s x) (p j) ^ a‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom (hsum.mul_right (1/3))
  have hb := (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hdom (hsum.mul_right (1/3)))
  rw [tsum_mul_right] at hb
  change ‖pole (c x) (s x) 3^a + ∑' j, pole (c x) (s x) (p j)^a‖ ≤ _
  have hthree := est 3 (by norm_num)
  rw [show envelope 3^4 = 1/16 by norm_num [envelope]] at hthree
  linarith [norm_add_le (pole (c x) (s x) 3^a) (∑' j, pole (c x) (s x) (p j)^a)]

private theorem cycle_pole_nearest_error (x : ℝ) (hx : 0 ≤ x) (a : ℕ) (ha : 8 ≤ a)
    (hs : 1 ≤ (a:ℝ)*s x^2) :
    |principalCycleMoment x a| ≤ cycleMomentScale x a ∧
      |cyclePoleMoment x a - principalCycleMoment x a| ≤ (1/9)*cycleMomentScale x a := by
  have ha' : (8:ℝ) ≤ a := by exact_mod_cast ha
  have hcast : (0:ℝ) ≤ a := by positivity
  have hre := complete_normalization x a a ha' hs (by linarith : (a:ℝ) ≤ 2*(a:ℝ))
  rw [← Complex.ofReal_pow] at hre
  have hreal := congrArg Complex.re hre
  simp [Complex.mul_re] at hreal
  have hfac : 0 ≤ cycleMomentScale x a :=
    div_nonneg (by positivity) (pow_nonneg (radius_pos x).le _)
  have heq : cyclePoleMoment x a = cycleMomentScale x a * (total (c x) (s x) a).re := by
    unfold cyclePoleMoment cycleMomentScale
    field_simp [(radius_pos x).ne']
    linear_combination ((a-1).factorial : ℝ) * hreal
  have hprincipal : ‖pole (c x) (s x) 1 ^ a‖ = 1 := by
    rw [norm_pole_pow _ _ _ (circle x) (by norm_num)]
    simp [amplitude]
  constructor
  · unfold principalCycleMoment
    rw [abs_mul, abs_of_nonneg hfac]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hprincipal.le) hfac).trans_eq (mul_one _)
  · rw [heq, principalCycleMoment, ← mul_sub, abs_mul, abs_of_nonneg hfac]
    have ht : (total (c x) (s x) a).re - (pole (c x) (s x) 1 ^ a).re = (tail (c x) (s x) a).re := by
      simp [total, Complex.add_re]
    rw [ht]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (pole_tail_bound x a ha hs)) hfac).trans_eq (mul_comm _ _)

/-- A bound for the literal row's nonprincipal profile error on the infinite
region where every allowed cycle length has the frozen single-cycle tail bound. -/
theorem original_nonprincipal_profile_bound (n k : ℕ) (hk : 8 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) (hs : 1 ≤ (k:ℝ)*s x^2) :
    |nonprincipalProfileRemainder n k x| ≤
      ∑ h ∈ range (n/k+1), (1/(h.factorial:ℝ)) *
        (((10/9 : ℝ)^h-1) * orderedMomentRow (cycleMomentScale x) n k h) := by
  have hcycle (a : ℕ) (hak : k ≤ a) :=
    cycle_pole_nearest_error x hx a (hk.trans hak)
      (hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hak) (sq_nonneg _)))
  rw [nonprincipalProfileRemainder, original_normalized_pole_profile n k (by omega) x hx,
    principalPoleProfile, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro h _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [show (1:ℝ) + 1/9 = 10/9 by norm_num] using
    (orderedMomentRow_approximation (k := k) (ε := (1:ℝ)/9) (by positivity)
      (fun _ _ => div_nonneg (by positivity) (pow_nonneg (radius_pos x).le _))
      (fun a hak => (hcycle a hak).1) (fun a hak => (hcycle a hak).2) n h).2

#print axioms original_normalized_pole_profile
#print axioms original_nonprincipal_profile_bound
end RepositoryQuotientAudit
