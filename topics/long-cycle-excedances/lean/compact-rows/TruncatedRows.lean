import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OpenMathResearch.LongCycleExcedances.TruncatedRows
open Finset

/-- Keep only the first b binary digits of a nonnegative coefficient. -/
def chop (b v : ℕ) : ℕ :=
  let unit := 2^(v.log2+1-b)
  v / unit * unit

theorem chop_le (b v : ℕ) : chop b v ≤ v := Nat.div_mul_le_self _ _

theorem chop_loss {b : ℕ} (hb : 0 < b) (v : ℕ) :
    (v - chop b v) * 2^(b-1) ≤ v := by
  by_cases hs : v.log2+1 ≤ b
  · simp [chop, Nat.sub_eq_zero_of_le hs]
  · have hv : v ≠ 0 := by
      intro h
      subst v
      simp at hs
      omega
    let e := v.log2+1-b
    have he : e + (b-1) = v.log2 := by dsimp [e]; omega
    have hmod := Nat.mod_add_div v (2^e)
    have hdiff : v - chop b v = v % (2^e) := by
      change v - v/(2^e)*(2^e) = _
      rw [Nat.mul_comm (v/(2^e))]
      omega
    rw [hdiff]
    calc
      _ ≤ 2^e * 2^(b-1) := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.mod_lt _ (by positivity)))
      _ = 2^v.log2 := by rw [← pow_add, he]
      _ ≤ _ := Nat.log2_self_le hv

/-- A one-sided relative enclosure, whose error grows by one unit per row. -/
def Within (eps : ℝ) (n : ℕ) (low actual : ℝ) : Prop :=
  0 ≤ low ∧ low ≤ actual ∧ (1 - n*eps)*actual ≤ low

theorem within_mono {eps low actual : ℝ} {m n : ℕ} (he : 0 ≤ eps)
    (hm : m ≤ n) (h : Within eps m low actual) : Within eps n low actual := by
  refine ⟨h.1,h.2.1,le_trans ?_ h.2.2⟩
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) he) 1) (h.1.trans h.2.1)

theorem positive_sum {ι : Type*} (t : Finset ι) {eps : ℝ} {n : ℕ}
    (weight low actual : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ weight i)
    (h : ∀ i ∈ t, Within eps n (low i) (actual i)) :
    Within eps n (∑ i ∈ t, weight i*low i) (∑ i ∈ t, weight i*actual i) := by
  refine ⟨sum_nonneg fun i hi => mul_nonneg (hw i hi) (h i hi).1,
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi).2.1 (hw i hi), ?_⟩
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  calc
    _ = weight i * ((1 - (n:ℝ)*eps)*actual i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h i hi).2.2 (hw i hi)

theorem round_step {eps low actual rounded : ℝ} {n : ℕ} (hu : eps ≤ 1)
    (h : Within eps n low actual) (hdown : rounded ≤ low) (hrel : (1-eps)*low ≤ rounded) :
    Within eps (n+1) rounded actual := by
  have ha : 0 ≤ actual := h.1.trans h.2.1
  refine ⟨(mul_nonneg (sub_nonneg.mpr hu) h.1).trans hrel, hdown.trans h.2.1, ?_⟩
  have hlo := mul_le_mul_of_nonneg_left h.2.2 (sub_nonneg.mpr hu)
  refine le_trans ?_ (hlo.trans hrel)
  push_cast
  have hcorr : 0 ≤ ((n:ℝ)*eps^2)*actual :=
    mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ha
  nlinarith only [hcorr]

theorem coefficient_error {eps low actual : ℝ} {n : ℕ} (he : 0 ≤ eps)
    (hsmall : (n:ℝ)*eps ≤ 1/2) (h : Within eps n low actual) :
    0 ≤ actual-low ∧ actual-low ≤ (2*n*eps)*low := by
  have ha := h.1.trans h.2.1
  have hbig : actual ≤ 2*low := by
    have := mul_le_mul_of_nonneg_right hsmall ha
    linarith [h.2.2]
  have := mul_le_mul_of_nonneg_left hbig (mul_nonneg (Nat.cast_nonneg n) he)
  exact ⟨sub_nonneg.mpr h.2.1, by nlinarith only [this,h.2.2]⟩

theorem chop_within_one {b : ℕ} (hb : 0 < b) (v : ℕ) :
    Within ((1 : ℝ)/2^(b-1)) 1 (chop b v : ℝ) (v : ℝ) := by
  have h : ((v - chop b v : ℕ) : ℝ) * (2 : ℝ)^(b-1) ≤ v := by
    exact_mod_cast chop_loss hb v
  rw [Nat.cast_sub (chop_le b v)] at h
  have err := (le_div_iff₀ (by positivity : (0:ℝ) < 2^(b-1))).mpr h
  refine ⟨by positivity, by exact_mod_cast chop_le b v, ?_⟩
  simp only [Nat.cast_one, one_mul]
  rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
  linarith

theorem signed_prefix_error {eps : ℝ} {n W : ℕ} (he : 0 ≤ eps)
    (hn : (n:ℝ)*eps ≤ 1/2) (y : ℝ) (hy : 0 ≤ y) (low actual : ℕ → ℝ)
    (h : ∀ i ∈ range W, Within eps n (low i) (actual i)) :
    |(∑ i ∈ range W, actual i*(-y)^i) - ∑ i ∈ range W, low i*(-y)^i| ≤
      (2*n*eps)*∑ i ∈ range W, low i*y^i := by
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro i hi
  obtain ⟨hne, hle⟩ := coefficient_error he hn (h i hi)
  rw [← sub_mul, abs_mul, abs_of_nonneg hne, abs_pow, abs_neg, abs_of_nonneg hy, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hle (pow_nonneg hy _)

theorem within_add {eps : ℝ} {n : ℕ} {a b x y : ℝ}
    (h : Within eps n a x) (g : Within eps n b y) : Within eps n (a+b) (x+y) := by
  refine ⟨add_nonneg h.1 g.1, add_le_add h.2.1 g.2.1, ?_⟩
  rw [mul_add]
  exact add_le_add h.2.2 g.2.2

theorem within_scale {eps : ℝ} {n : ℕ} {a x : ℝ} (s : ℝ) (hs : 0 ≤ s)
    (h : Within eps n a x) : Within eps n (s*a) (s*x) := by
  refine ⟨mul_nonneg hs h.1, mul_le_mul_of_nonneg_left h.2.1 hs, ?_⟩
  calc
    _ = s*((1-(n:ℝ)*eps)*x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h.2.2 hs

def positiveStep (k n : ℕ) (a p r : ℕ → ℕ) : ℕ → ℕ
  | 0 => p 0
  | i+1 => (i+2)*p (i+1) + (n-(i+1))*p i +
      n.choose (k-1) * ∑ j ∈ range (i+1), a j * r (i-j)

/-- One step uses nonnegative weights even beyond the true row degree. A
separate coefficient interpretation identifies the zero-padded tails. -/
theorem approx_positive_step {b w k n : ℕ} (hb : 0 < b) (a p r P R : ℕ → ℕ)
    (hp : ∀ j, j<w → Within (1/2^(b-1)) n (p j) (P j))
    (hr : ∀ j, j<w → Within (1/2^(b-1)) n (r j) (R j)) (i : ℕ) (hi : i<w) :
    Within (1/2^(b-1)) (n+1) (chop b (positiveStep k n a p r i) : ℕ)
      (positiveStep k n a P R i : ℕ) := by
  let eps : ℝ := 1/2^(b-1)
  have hε : eps ≤ 1 := by dsimp [eps]; exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have h : Within eps n (positiveStep k n a p r i : ℕ) (positiveStep k n a P R i : ℕ) := by
    cases i with
    | zero => exact hp 0 hi
    | succ j =>
      have hsum := positive_sum (range (j+1)) (eps:=eps) (n:=n) (fun h => (a h : ℝ))
        (fun h => (r (j-h) : ℝ)) (fun h => (R (j-h) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (fun h _ => hr (j-h) (by omega))
      have h1 := within_scale ((j+2 : ℕ) : ℝ) (Nat.cast_nonneg _) (hp (j+1) hi)
      have h2 := within_scale ((n-(j+1) : ℕ) : ℝ) (Nat.cast_nonneg _) (hp j (by omega))
      have h3 := within_scale (n.choose (k-1) : ℝ) (Nat.cast_nonneg _) hsum
      simp only [positiveStep, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
      simpa only [Nat.cast_add, Nat.cast_one, eps] using within_add (within_add h1 h2) h3
  have hchop := chop_within_one hb (positiveStep k n a p r i)
  apply round_step hε h hchop.2.1
  simpa only [Nat.cast_one, one_mul, eps] using hchop.2.2

/-- The exact recurrence, rounded recurrence and single-cycle seed imply the
relative enclosure at every subsequent size, also when the lag is still zero. -/
theorem all_rows_within {b w k : ℕ} (hb : 0 < b) (hk : 0 < k) (a : ℕ → ℕ)
    (exactRow low : ℕ → ℕ → ℕ)
    (short : ∀ n, n<k → ∀ i, i<w → exactRow n i=0 ∧ low n i=0)
    (seed : ∀ i, i<w → low k i = chop b (exactRow k i))
    (step : ∀ m, k≤m → ∀ i, i<w →
      exactRow (m+1) i = positiveStep k m a (exactRow m) (exactRow (m+1-k)) i ∧
      low (m+1) i = chop b (positiveStep k m a (low m) (low (m+1-k)) i)) :
    ∀ n i, i<w → Within (1/2^(b-1)) n (low n i) (exactRow n i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hi
    rcases lt_trichotomy n k with h | h | h
    · obtain ⟨he,hl⟩ := short n h i hi
      simp [he,hl,Within]
    · subst n
      rw [seed _ hi]
      exact within_mono (by positivity) hk (chop_within_one hb _)
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨he,hl⟩ := step m (by omega) i hi
      rw [he,hl]
      apply approx_positive_step hb a (low m) (low (m+1-k)) (exactRow m)
        (exactRow (m+1-k)) _ _ i hi
      · exact ih m (by omega)
      · intro j hj
        apply within_mono (by positivity) (by omega : m+1-k ≤ m)
        exact ih _ (by omega) j hj

theorem uniform_error_factor {b n : ℕ} (hb : 12 ≤ b) (hn : n ≤ 1024) :
    2*(n:ℝ)*(1/2^(b-1)) ≤ 1/2^(b-12) := by
  have he : b-1 = b-12+11 := by omega
  rw [he, pow_add, ← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hu : (n : ℝ) ≤ 1024 := by exact_mod_cast hn
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ (2:ℝ)^(b-12))]

#print axioms all_rows_within
#print axioms uniform_error_factor

#print axioms approx_positive_step

#print axioms chop_within_one
#print axioms signed_prefix_error
#print axioms chop_loss
#print axioms positive_sum
#print axioms round_step
#print axioms coefficient_error
end OpenMathResearch.LongCycleExcedances.TruncatedRows
