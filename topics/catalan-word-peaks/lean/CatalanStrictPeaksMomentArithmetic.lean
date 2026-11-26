import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic for the effective Catalan cut estimates

The first statement checks the local bound after the first two beta
moments are inserted. The tail bounds use the four residue classes of the
cut exponent and check each initial case exactly.
-/

namespace CatalanStrictPeaks.CutBounds

/-- The rational estimate at the right of the short-range beta-moment bound. -/
theorem near_moment_bound {n : ℝ} (hn : 150 ≤ n) :
    (2 * n / 5 + 9) * ((3 / 2) / (n - 3 / 2)) +
      (2 * n / 5 + 4 / 5) * ((15 / 4) / ((n - 3 / 2) * (n - 5 / 2))) < 71 / 100 := by
  have h₁ : 0 < n - 3 / 2 := by linarith
  have h₂ : 0 < n - 5 / 2 := by linarith
  have hδ : 0 ≤ n - 150 := sub_nonneg.mpr hn
  have hclear :
      (71 / 100 : ℝ) * ((n - 3 / 2) * (n - 5 / 2)) -
        ((2 * n / 5 + 9) * ((3 / 2) / (n - 3 / 2)) +
          (2 * n / 5 + 4 / 5) * ((15 / 4) / ((n - 3 / 2) * (n - 5 / 2)))) *
          ((n - 3 / 2) * (n - 5 / 2)) =
      (11 / 100) * (n - 150) ^ 2 + (833 / 50) * (n - 150) + 4593 / 80 := by
    have hcancel₁ :
        ((3 / 2 : ℝ) / (n - 3 / 2)) * ((n - 3 / 2) * (n - 5 / 2)) =
          (3 / 2) * (n - 5 / 2) := by
      rw [← mul_assoc, div_mul_cancel₀ _ h₁.ne']
    have hcancel₂ :
        ((15 / 4 : ℝ) / ((n - 3 / 2) * (n - 5 / 2))) * ((n - 3 / 2) * (n - 5 / 2)) =
          15 / 4 := div_mul_cancel₀ _ (mul_pos h₁ h₂).ne'
    rw [add_mul, mul_assoc (2 * n / 5 + 9), mul_assoc (2 * n / 5 + 4 / 5),
      hcancel₁, hcancel₂]
    ring
  have hpos : 0 < (11 / 100 : ℝ) * (n - 150) ^ 2 + (833 / 50) * (n - 150) + 4593 / 80 := by positivity
  apply (mul_lt_mul_right (mul_pos h₁ h₂)).mp
  linarith

/-- n minus the least integer at least n/4. -/
def cutExponent (n : ℕ) : ℕ := n - (n + 3) / 4

theorem cutExponent_add_four (n : ℕ) : cutExponent (n + 4) = cutExponent n + 3 := by
  unfold cutExponent
  omega

/-- The tail cost before comparison against a fixed rational bound. -/
noncomputable def tailScore (p : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  60 * (n : ℝ) ^ p * q ^ cutExponent n

private theorem tailScore_step {p : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hloss : (154 / 150 : ℝ) ^ p * q ^ 3 ≤ 1) {n : ℕ} (hn : 150 ≤ n) :
    tailScore p q (n + 4) ≤ tailScore p q n := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hratio : ((n : ℝ) + 4) ≤ (154 / 150 : ℝ) * (n : ℝ) := by linarith
  unfold tailScore
  rw [cutExponent_add_four, pow_add, Nat.cast_add, Nat.cast_ofNat]
  have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 4 by positivity) hratio p
  calc
    _ ≤ 60 * ((154 / 150 : ℝ) * (n : ℝ)) ^ p * (q ^ cutExponent n * q ^ 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
    _ = (60 * (n : ℝ) ^ p * q ^ cutExponent n) * ((154 / 150 : ℝ) ^ p * q ^ 3) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hloss

private theorem tailScore_control {p : ℕ} {q bound : ℝ} (hq : 0 ≤ q)
    (hloss : (154 / 150 : ℝ) ^ p * q ^ 3 ≤ 1)
    (hbase : ∀ n, 150 ≤ n → n < 154 → tailScore p q n < bound)
    (n : ℕ) (hn : 150 ≤ n) : tailScore p q n < bound := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 154
    · exact hbase n hn h
    · let m := n - 4
      have hmn : m < n := by omega
      have hm : 150 ≤ m := by omega
      have heq : n = m + 4 := by omega
      calc
        tailScore p q n = tailScore p q (m + 4) := by rw [← heq]
        _ ≤ tailScore p q m := tailScore_step hq hloss hm
        _ < bound := ih m hmn hm

/-- The exponential tail estimate for displacement at least one eighth. -/
theorem near_tail_bound (n : ℕ) (hn : 150 ≤ n) :
    tailScore 1 (8 / 9) n < 1 / 50 := by
  apply tailScore_control (by norm_num) (by norm_num) _ n hn
  intro k hk hK
  have h : k = 150 ∨ k = 151 ∨ k = 152 ∨ k = 153 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [tailScore, cutExponent]

/-- The exponential tail estimate, multiplied by n, for the covariance bound. -/
theorem covariance_tail_bound (n : ℕ) (hn : 150 ≤ n) :
    tailScore 2 (6 / 7) n < 1 / 20 := by
  apply tailScore_control (by norm_num) (by norm_num) _ n hn
  intro k hk hK
  have h : k = 150 ∨ k = 151 ∨ k = 152 ∨ k = 153 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> norm_num [tailScore, cutExponent]

end CatalanStrictPeaks.CutBounds
