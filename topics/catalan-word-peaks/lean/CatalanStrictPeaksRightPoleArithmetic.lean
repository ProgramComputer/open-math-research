import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational arithmetic for the rightmost Catalan root

The two pole expansions give quantitative control of the logarithmic
derivative at the coalescence point.
-/

namespace CatalanStrictPeaks.RightEdge

private theorem relative_tail {n : ℕ} (hn : 150 ≤ n) :
    24 * (8 / 9 : ℝ) ^ n ≤ (11 / 16 : ℝ) / 100 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num) hn
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)

private theorem exponential_dominates {n : ℕ} (hn : 150 ≤ n) :
    1000 * (n : ℝ) ^ 3 < (4 / 3 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : ((n : ℝ) + 1) ^ 3 ≤ (4 / 3) * (n : ℝ) ^ 3 := by
      calc
        _ ≤ ((151 / 150 : ℝ) * (n : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (151 / 150 : ℝ) ^ 3 * (n : ℝ) ^ 3 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    push_cast
    rw [pow_succ]
    calc
      _ ≤ (1000 * (n : ℝ) ^ 3) * (4 / 3) := by linarith
      _ < _ := mul_lt_mul_of_pos_right ih (by norm_num)

private theorem pole_ratio_bounds (v d : ℕ → ℝ) {K : ℝ} (hK : 1 < K) {n : ℕ}
    (hn : 150 ≤ n)
    (hv : |v n - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n)
    (hd : |d n - K * (9 / 4 : ℝ) ^ n| ≤ 20 * (n : ℝ) * (27 / 16 : ℝ) ^ n) :
    0 < v n ∧
      K * (4 / 3 : ℝ) ^ n / (1111 / 1600) - 20 * (n : ℝ) / (1089 / 1600) ≤ d n / v n ∧
      d n / v n ≤ K * (4 / 3 : ℝ) ^ n / (1089 / 1600) + 20 * (n : ℝ) / (1089 / 1600) := by
  let a : ℝ := (27 / 16) ^ n
  let P := v n / a
  let E := (d n - K * (9 / 4 : ℝ) ^ n) / a
  let L : ℝ := 1089 / 1600
  let U : ℝ := 1111 / 1600
  have ha : 0 < a := by dsimp [a]; positivity
  have herror : |P - 11 / 16| ≤ 11 / 16 / 100 := by
    have heq : P - 11 / 16 = (v n - (11 / 16) * a) / a := by
      dsimp [P]
      field_simp [ha.ne']
      ring
    rw [heq, abs_div, abs_of_pos ha]
    calc
      _ ≤ (24 * (3 / 2 : ℝ) ^ n) / a := div_le_div_of_nonneg_right hv ha.le
      _ = 24 * (8 / 9 : ℝ) ^ n := by
        dsimp only [a]
        rw [mul_div_assoc, ← div_pow]
        norm_num
      _ ≤ _ := relative_tail hn
  obtain ⟨h₁, h₂⟩ := abs_le.mp herror
  have hL : L ≤ P := by dsimp [L]; linarith
  have hU : P ≤ U := by dsimp [U]; linarith
  have hP : 0 < P := (show 0 < L by norm_num [L]).trans_le hL
  have hpos : 0 < v n := (div_pos_iff_of_pos_right ha).mp hP
  have hE : |E| ≤ 20 * (n : ℝ) := by
    dsimp only [E]
    rw [abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hd
  obtain ⟨he₁, he₂⟩ := abs_le.mp hE
  have hlead : 0 ≤ K * (4 / 3 : ℝ) ^ n := by positivity
  have hquot : d n / v n = (K * (4 / 3 : ℝ) ^ n + E) / P := by
    have hfactor : (9 / 4 : ℝ) ^ n / a = (4 / 3 : ℝ) ^ n := by
      dsimp only [a]
      rw [← div_pow]
      norm_num
    rw [← hfactor, ← mul_div_assoc]
    dsimp only [E, P]
    rw [← add_div]
    field_simp [ha.ne', hpos.ne']
  have hminus : -(20 * (n : ℝ) / L) ≤ E / P := by
    calc
      _ = -(20 * (n : ℝ)) / L := by ring
      _ ≤ -(20 * (n : ℝ)) / P := by
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num [L]) hL
      _ ≤ _ := div_le_div_of_nonneg_right he₁ hP.le
  have hplus : E / P ≤ 20 * (n : ℝ) / L :=
    (div_le_div_of_nonneg_right he₂ hP.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num [L]) hL)
  refine ⟨hpos, ?_, ?_⟩
  · rw [hquot, add_div, sub_eq_add_neg]
    exact add_le_add (div_le_div_of_nonneg_left hlead hP hU) hminus
  · rw [hquot, add_div]
    exact add_le_add (div_le_div_of_nonneg_left hlead (by norm_num [L]) hL) hplus

/-- The coefficient estimates imply the absolute and successive logarithmic
derivative bounds required for the rightmost root. -/
theorem ratio_growth_of_poles (v d : ℕ → ℝ) {K : ℝ} (hK : 1 < K)
    (hv : ∀ n, 150 ≤ n → |v n - (11 / 16 : ℝ) * (27 / 16 : ℝ) ^ n| ≤ 24 * (3 / 2 : ℝ) ^ n)
    (hd : ∀ n, 150 ≤ n → |d n - K * (9 / 4 : ℝ) ^ n| ≤ 20 * (n : ℝ) * (27 / 16 : ℝ) ^ n)
    {n : ℕ} (hn : 150 ≤ n) :
    0 < v n ∧ 300 * (n : ℝ) ^ 3 < d n / v n ∧
      100 * (n : ℝ) ^ 3 < d (n + 1) / v (n + 1) - d n / v n := by
  have hn' : 150 ≤ n + 1 := by omega
  obtain ⟨hpos, hlow, hhigh⟩ := pole_ratio_bounds v d hK hn (hv n hn) (hd n hn)
  obtain ⟨_, hlow', _⟩ := pole_ratio_bounds v d hK hn' (hv (n + 1) hn') (hd (n + 1) hn')
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpow : 0 < (4 / 3 : ℝ) ^ n := by positivity
  have hgrowth := exponential_dominates hn
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith only [hnR]
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      simpa using pow_le_pow_left₀ zero_le_one h1 2
    calc
      _ = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hn0
      _ = _ := by ring
  have hmain : (4 / 3 : ℝ) ^ n < K * (4 / 3 : ℝ) ^ n / (1111 / 1600) := by
    apply (lt_div_iff₀ (show (0 : ℝ) < 1111 / 1600 by norm_num)).mpr
    have h : (1111 / 1600 : ℝ) < K := by linarith only [hK]
    simpa only [mul_comm] using mul_lt_mul_of_pos_right h hpow
  let c : ℝ := (4 / 3) / (1111 / 1600) - 1 / (1089 / 1600)
  have hc : (3 / 10 : ℝ) < c := by norm_num [c]
  have hcomp : (3 / 10) * (4 / 3 : ℝ) ^ n <
      K * (4 / 3 : ℝ) ^ (n + 1) / (1111 / 1600) -
        K * (4 / 3 : ℝ) ^ n / (1089 / 1600) := by
    have heq : K * (4 / 3 : ℝ) ^ (n + 1) / (1111 / 1600) -
        K * (4 / 3 : ℝ) ^ n / (1089 / 1600) = K * (4 / 3 : ℝ) ^ n * c := by
      rw [pow_succ]
      dsimp only [c]
      ring
    rw [heq]
    calc
      _ < c * (4 / 3 : ℝ) ^ n := mul_lt_mul_of_pos_right hc hpow
      _ = 1 * (4 / 3 : ℝ) ^ n * c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK.le hpow.le) (by norm_num [c])
  push_cast at hlow'
  exact ⟨hpos, by linarith only [hlow, hmain, hcube, hgrowth],
    by linarith only [hlow', hhigh, hcomp, hcube, hgrowth, hnR]⟩

end CatalanStrictPeaks.RightEdge
