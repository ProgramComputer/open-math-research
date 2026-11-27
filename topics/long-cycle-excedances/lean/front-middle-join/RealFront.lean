import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace OpenMathResearch.LongCycleExcedances
open Set

/-- Cross-multiplied form of the adaptive-radius identity with inverse growth q. -/
theorem adjacent_front_centers
    {u v ρ σ q R : ℝ} (hu : 0 < u) (hρ : 0 < ρ) (hq : 0 < q)
    (hρR : ρ ≤ R) (hσ : 1 ≤ R * σ) (hR : 0 < R)
    (hsmall : 20 * R ^ 2 * q < 1)
    (hratio : ρ * q * v = σ * u) :
    20 * u < v := by
  have hbound : 20 * (ρ * q) * R < 1 := by
    calc
      20 * (ρ * q) * R ≤ 20 * (R * q) * R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρR hq.le) (by norm_num))
          hR.le
      _ = 20 * R ^ 2 * q := by ring
      _ < 1 := hsmall
  have hcoeff : 20 * (ρ * q) < σ := by
    apply lt_of_mul_lt_mul_right _ hR.le
    calc
      20 * (ρ * q) * R < 1 := hbound
      _ ≤ σ * R := by simpa [mul_comm] using hσ
  apply lt_of_mul_lt_mul_left _ (mul_nonneg hρ.le hq.le)
  calc
    ρ * q * (20 * u) = (20 * (ρ * q)) * u := by ring
    _ < σ * u := mul_lt_mul_of_pos_right hcoeff hu
    _ = ρ * q * v := hratio.symm

/-- The constants used by the effective front, with q bounded by the
inverse adjacent growth. -/
theorem effective_front_adjacent_centers
    {u v ρ σ q : ℝ} (hu : 0 < u) (hρ : 0 < ρ) (hq : 0 < q)
    (hρR : ρ ≤ 51 / 5) (hσ : 1 ≤ (51 / 5) * σ)
    (hqmax : q ≤ 1 / 2200) (hratio : ρ * q * v = σ * u) :
    20 * u < v := by
  refine adjacent_front_centers hu hρ hq hρR hσ (by norm_num) ?_ hratio
  linarith

theorem front_boxes_ordered {H : ℕ} (u : ℕ → ℝ)
    (hu : ∀ h < H, 0 < u h)
    (hgap : ∀ h, h + 1 < H → 20 * u h < u (h + 1)) :
    ∀ i j, i < j → j < H → (9 / 8 : ℝ) * u i < (7 / 8 : ℝ) * u j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hj' : j < H := by omega
    have hp := hu j hj'
    have hg := hgap j hj
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with he | hl
    · subst i
      linarith
    · have hi := ih hl hj'
      linarith

/-- A negative normalized derivative, even after adding the normalized lag,
gives the actual successor quotient sign at an old root. -/
theorem front_successor_sign {h : ℕ} {a x d lag Q : ℝ}
    (ha : 0 < a) (hx : x < 0)
    (hd : |d + 1| < 3 / 20) (hlag : |lag| ≤ 18 / 25)
    (hins : x * Q = ((1 - x) * (a * x ^ h)) * (d + lag)) :
    0 < (-1 : ℝ) ^ h * Q := by
  have hsum : d + lag < 0 := by
    linarith [(abs_lt.mp hd).2, (abs_le.mp hlag).2]
  have hsignpow : (-1 : ℝ) ^ h * x ^ h = (-x) ^ h := by
    rw [← mul_pow]
    simp
  have hxpos : 0 < -x := neg_pos.mpr hx
  have hm : x * ((-1 : ℝ) ^ h * Q) = ((1 - x) * (a * (-x) ^ h)) * (d + lag) := by
    calc
      _ = (-1 : ℝ) ^ h * (x * Q) := by ring
      _ = ((1 - x) * (a * ((-1 : ℝ) ^ h * x ^ h))) * (d + lag) := by rw [hins]; ring
      _ = _ := by rw [hsignpow]
  have hc : 0 < (1 - x) * (a * (-x) ^ h) :=
    mul_pos (by linarith) (mul_pos ha (pow_pos hxpos h))
  have hn : x * ((-1 : ℝ) ^ h * Q) < 0 := hm ▸ mul_neg_of_pos_of_neg hc hsum
  exact (pos_of_mul_neg_right hn hx.le)

/-- Convert the raw insertion and lag inequality at a zero to the
normalization used by the singleton lemma. -/
theorem front_normalize_insertion {h : ℕ} {a x d rawLag Q : ℝ}
    (ha : 0 < a) (hx : x < 0)
    (hlag : |rawLag| ≤ (18 / 25) * |a * x ^ h|)
    (hins : x * Q = ((1 - x) * (a * x ^ h)) * d + rawLag) :
    let B := a * x ^ h
    let C := (1 - x) * B
    |rawLag / C| ≤ 18 / 25 ∧ x * Q = C * (d + rawLag / C) := by
  dsimp only
  have hscale : 0 < 1 - x := by linarith
  have hB : a * x ^ h ≠ 0 := mul_ne_zero ha.ne' (pow_ne_zero h hx.ne)
  have hC : (1 - x) * (a * x ^ h) ≠ 0 := mul_ne_zero hscale.ne' hB
  constructor
  · rw [abs_div, div_le_iff₀ (abs_pos.mpr hC), abs_mul, abs_of_pos hscale]
    have hmul : |a * x ^ h| ≤ (1 - x) * |a * x ^ h| := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 - x by linarith)
          (abs_nonneg (a * x ^ h))
    exact hlag.trans (mul_le_mul_of_nonneg_left hmul (by norm_num))
  · rw [hins, mul_add, ← mul_div_assoc, mul_comm ((1 - x) * (a * x ^ h)) rawLag,
      mul_div_cancel_right₀ _ hC]

/-- Real two-term bounds and the insertion identity at old zeros supply a singleton.
The variable v is the positive point in the normalized old box. -/
theorem front_singleton_witness {h : ℕ} {a u : ℝ}
    (F D lag P Q : ℝ → ℝ) (ha : 0 < a) (hu : 0 < u)
    (hcont : ContinuousOn F (Icc (7 / 8 : ℝ) (9 / 8)))
    (herr : ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8), |F v - (1 - v)| < 1 / 10)
    (hd : ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8), F v = 0 → |D v + 1| < 3 / 20)
    (hlag : ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8), F v = 0 → |lag v| ≤ 18 / 25)
    (hold : ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8), F v = 0 → P (-(u * v)) = 0)
    (hins : ∀ v ∈ Icc (7 / 8 : ℝ) (9 / 8), F v = 0 →
      let x := -(u * v)
      x * Q x = ((1 - x) * (a * x ^ h)) * (D v + lag v)) :
    ∃ w ∈ Icc ((7 / 8 : ℝ) * u) ((9 / 8 : ℝ) * u),
      P (-w) = 0 ∧ 0 < (-1 : ℝ) ^ h * Q (-w) := by
  have he : (7 / 8 : ℝ) ≤ 9 / 8 := by norm_num
  have left : 0 < F (7 / 8) := by
    linarith [(abs_lt.mp (herr _ ⟨le_rfl, he⟩)).1]
  have right : F (9 / 8) < 0 := by
    linarith [(abs_lt.mp (herr _ ⟨he, le_rfl⟩)).2]
  obtain ⟨v, hv, hz⟩ := intermediate_value_Icc' he hcont (show (0 : ℝ) ∈
    Icc (F (9 / 8)) (F (7 / 8)) from ⟨right.le, left.le⟩)
  have hp : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
  refine ⟨u * v, ⟨?_, ?_⟩, hold v hv hz, ?_⟩
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hv.1 hu.le
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hv.2 hu.le
  · exact front_successor_sign ha (neg_neg_of_pos (mul_pos hu hp))
      (hd v hv hz) (hlag v hv hz) (hins v hv hz)

#print axioms adjacent_front_centers
#print axioms effective_front_adjacent_centers
#print axioms front_boxes_ordered
#print axioms front_successor_sign
#print axioms front_normalize_insertion
#print axioms front_singleton_witness

end OpenMathResearch.LongCycleExcedances
