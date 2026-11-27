import UniformDiscreteTilt

noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def scaledFrequency (R x : ℝ) (d i : ℕ) : ℝ :=
  let a : ℝ := (i+1:ℕ)
  (a^(d-1)*exp (-x*a)) * (R^d/(d.factorial:ℝ))

private theorem freq_nonneg {R x : ℝ} (hR : 0 ≤ R) (d i : ℕ) :
    0 ≤ scaledFrequency R x d i := by unfold scaledFrequency; positivity

private theorem freq_summable {R x : ℝ} (hx : 0 < x) (d : ℕ) :
    Summable (scaledFrequency R x d) := by
  exact ((summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul (d-1) hx)).mul_right _

private theorem bound_moment_sum {R x : ℝ} (hR : 0 ≤ R) (hx : 0 < x) (d : ℕ)
    (m : ℝ) (h : m = ∑' i : ℕ, (-1:ℝ)^(i+1)*((i+1:ℕ):ℝ)^(d-1)*exp (-x*(i+1:ℕ))) :
    |(-m/(d.factorial:ℝ))*R^d| ≤ ∑' i, scaledFrequency R x d i := by
  let v (i : ℕ) := (-1:ℝ)^(i+1)*((i+1:ℕ):ℝ)^(d-1)*exp (-x*(i+1:ℕ))
  have he (i : ℕ) : ‖v i * (R^d/(d.factorial:ℝ))‖ = scaledFrequency R x d i := by
    dsimp [v,scaledFrequency]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i+1)), abs_of_nonneg (exp_pos _).le,
      abs_of_nonneg (show 0 ≤ R^d/(d.factorial:ℝ) by positivity)]
  have hs : Summable fun i => ‖v i * (R^d/(d.factorial:ℝ))‖ := by
    simp only [he]
    exact freq_summable hx d
  have hb := norm_tsum_le_tsum_norm hs
  rw [tsum_mul_right, Real.norm_eq_abs] at hb
  simp only [he] at hb
  change m = ∑' i, v i at h
  rw [←h] at hb
  have hid : (-m/(d.factorial:ℝ))*R^d = -(m*(R^d/(d.factorial:ℝ))) := by ring
  rwa [hid, abs_neg]

/-- This puts the radius and factorial inside the discrete moment formula, so
a finite band of alternating Eulerian moments is controlled by one positive
truncated exponential. -/
theorem low_moment_absolute_mass {L k : ℕ} {R x : ℝ} (hk : 1 ≤ k)
    (hL : L ≤ k) (hx : 10 ≤ x) (hR : 0 ≤ R) (hsmall : 16*(L:ℝ) ≤ x^2)
    (hdelta : R-x ≤ 5/x+x/(40*(k:ℝ))) (hratio : R ≤ (53/50)*x)
    (m : ℕ → ℝ)
    (moment : ∀ d ∈ Icc 2 L, m d = ∑' i : ℕ,
      (-1:ℝ)^(i+1)*((i+1:ℕ):ℝ)^(d-1)*exp (-x*(i+1:ℕ))) :
    (∑ d ∈ Icc 2 L, |(-m d/(d.factorial:ℝ))*R^d|) ≤
      3 * (∑ i ∈ range k, (1:ℝ)/(i+1:ℕ)) + 1 := by
  have hx' : 0 < x := by linarith
  have hfreq (d : ℕ) (_ : d ∈ Icc 2 L) := freq_summable (R:=R) hx' d
  have hb := sum_le_sum (s := Icc 2 L) (fun d hd => bound_moment_sum hR hx' d (m d) (moment d hd))
  rw [← Summable.tsum_finsetSum hfreq] at hb
  apply hb.trans
  apply le_trans _ (discrete_low_frequency_sum hk hL hx hR hsmall hdelta hratio)
  let envelope (i : ℕ) := exp (-(((i+1:ℕ):ℝ)*x)) * expPrefix L (((i+1:ℕ):ℝ)*R) / (i+1:ℕ)
  have he (i : ℕ) : envelope i =
      ∑ d ∈ range (L+1), exp (-x*(i+1:ℕ))/(i+1:ℕ) * ((((i+1:ℕ):ℝ)*R)^d/(d.factorial:ℝ)) := by
    unfold envelope expPrefix
    rw [←mul_sum, mul_div_right_comm]
    congr 2
    ring
  have hen : Summable envelope := by
    let w (i : ℕ) := if i < k then (3:ℝ)/(i+1:ℕ) else 0
    have hw : Summable w := summable_of_ne_finset_zero (s := range k)
      (fun i hi => by simp [w, show ¬i<k from fun h => hi (mem_range.mpr h)])
    have hsum := hw.add ((summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)))
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro i
      exact div_nonneg (mul_nonneg (exp_pos _).le (expPrefix_nonneg _ (by positivity))) (by positivity)
    · intro i
      simpa only [w,Nat.succ_le_iff] using
        discrete_low_mode (Nat.succ_pos i) hk hL hx hR hsmall hdelta hratio
  apply (summable_sum hfreq).tsum_le_tsum _ hen
  intro i
  rw [he]
  have hi : (0:ℝ) < ((i+1:ℕ):ℝ) := by positivity
  let F (d : ℕ) := exp (-x*(i+1:ℕ))/(i+1:ℕ) * ((((i+1:ℕ):ℝ)*R)^d/(d.factorial:ℝ))
  apply le_trans (b := ∑ d ∈ Icc 2 L, F d) _ (sum_le_sum_of_subset_of_nonneg
    (by intro d hd; exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hd).2))
    (fun d _ _ => by dsimp [F]; positivity))
  apply sum_le_sum
  intro d hd
  have hd' : 0 < d := by have := (mem_Icc.mp hd).1; omega
  apply le_of_eq
  dsimp only [scaledFrequency,F]
  rw [mul_pow, show ((i+1:ℕ):ℝ)^d = ((i+1:ℕ):ℝ)^(d-1)*((i+1:ℕ):ℝ) by
    rw [←pow_succ, Nat.sub_add_cancel hd']]
  field_simp [hi.ne'] <;> ring

#print axioms low_moment_absolute_mass
end OpenMathResearch.LongCycleExcedances
