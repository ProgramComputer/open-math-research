import PrimitivePoleKernel

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def oBase (c p : ℝ) := 1+c*(p^2-1)
def oTail (c p : ℝ) := ((oBase c p)^95)⁻¹
def oWeight (c p : ℝ) := ((oBase c p)^96)⁻¹

/-- The exact checker tail follows from one discrete Bernoulli step.
The extra guard is met at the worst coefficient shape of both checkers. -/
theorem odd_step_le_tail_difference {c P p : ℝ} (hc : 0<c) (hP : 1≤P)
    (hg : 1≤3*c*P^2) (hp : P+2≤p) :
    380*c*p*oWeight c p ≤ oTail c (p-2)-oTail c p := by
  let B := oBase c p
  let B₀ := oBase c (p-2)
  have hB : 0 < B := by
    dsimp [B,oBase]
    have hh : 0 ≤ p^2-1 := by nlinarith
    positivity
  have hB₀ : 0 < B₀ := by
    dsimp [B₀,oBase]
    have hh : 0 ≤ (p-2)^2-1 := by nlinarith
    positivity
  have hΔ : B-B₀ = 4*c*(p-1) := by dsimp [B,B₀,oBase]; ring
  have hp1 : 0 < p-1 := by linarith
  have hBsub : 0 ≤ B-B₀ := by rw [hΔ]; positivity
  have hcurve : (1:ℝ) ≤ c*(3*p^2-4*p+1) := by
    have bell := mul_nonneg (sub_nonneg.mpr hp : 0 ≤ p-(P+2))
      (show 0 ≤ 3*(p+P)+2 by linarith)
    have hcur : 3*P^2 ≤ 3*p^2-4*p+1 := by nlinarith only [bell,hP]
    exact hg.trans ((by ring : 3*c*P^2 = c*(3*P^2)) ▸
      mul_le_mul_of_nonneg_left hcur hc.le)
  have hgain : p/(p-1) ≤ B/B₀ := by
    apply (div_le_div_iff₀ hp1 hB₀).mpr
    have hex : B*(p-1)-p*B₀ = c*(3*p^2-4*p+1)-1 := by dsimp [B,B₀,oBase]; ring
    linarith only [hex,hcurve]
  have hratio : 1 ≤ B/B₀ := (one_le_div hB₀).mpr (sub_nonneg.mp hBsub)
  have hbern := one_add_mul_self_le_rpow_one_add (by linarith only [hratio] : -1 ≤ B/B₀-1)
    (by norm_num : (1:ℝ) ≤ (95:ℕ))
  rw [show 1+(B/B₀-1)=B/B₀ by ring, Real.rpow_natCast] at hbern
  have hdiff : 95*((B-B₀)/B₀)*(B^95)⁻¹ ≤ (B₀^95)⁻¹-(B^95)⁻¹ := by
    have simple : (B/B₀)^95*(B^95)⁻¹ = (B₀^95)⁻¹ := by
      rw [div_pow,div_eq_mul_inv]
      field_simp [ne_of_gt (pow_pos hB 95),ne_of_gt (pow_pos hB₀ 95)]
      <;> ring
    have hh := mul_le_mul_of_nonneg_right hbern (inv_nonneg.mpr (pow_nonneg hB.le 95))
    rw [simple] at hh
    have he : B/B₀-1 = (B-B₀)/B₀ := by field_simp [hB₀.ne'] <;> ring
    rw [he,add_mul,one_mul] at hh
    linarith only [hh]
  have hm : p ≤ (p-1)*(B/B₀) := (div_le_iff₀ hp1).mp hgain |> (fun h => by simpa only [mul_comm] using h)
  have heq : 95*((B-B₀)/B₀)*(B^95)⁻¹ = 380*c*((p-1)*(B/B₀))*(B^96)⁻¹ := by
    rw [hΔ,show (96:ℕ)=95+1 by decide,pow_succ]
    field_simp [hB.ne',hB₀.ne',ne_of_gt (pow_pos hB 95)]
    <;> ring
  calc
    _ ≤ 380*c*((p-1)*(B/B₀))*(B^96)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)
    _ = 95*((B-B₀)/B₀)*(B^95)⁻¹ := heq.symm
    _ ≤ _ := hdiff

theorem odd_tail_finite_prefix {c P : ℝ} (hc : 0<c) (hP : 1≤P)
    (hg : 1≤3*c*P^2) (M : ℕ) :
    (∑ j ∈ range M, (P+2*((j:ℝ)+1))*oWeight c (P+2*((j:ℝ)+1))) ≤
      oTail c P/(380*c) := by
  have hb (m : ℕ) :
      380*c*(∑ j ∈ range m, (P+2*((j:ℝ)+1))*oWeight c (P+2*((j:ℝ)+1))) ≤
        oTail c P-oTail c (P+2*(m:ℝ)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ,mul_add,Nat.cast_succ]
      have h := odd_step_le_tail_difference hc hP hg
        (show P+2 ≤ P+2*((m:ℝ)+1) by linarith [Nat.cast_nonneg (α:=ℝ) m])
      rw [show P+2*((m:ℝ)+1)-2=P+2*(m:ℝ) by ring] at h
      linarith only [ih,h]
  apply (le_div_iff₀ (by positivity : 0<380*c)).mpr
  rw [mul_comm]
  apply (hb M).trans
  exact sub_le_self _ (inv_nonneg.mpr (by
    dsimp [oBase]
    have hh : (0:ℝ) ≤ (P+2*(M:ℝ))^2-1 := by nlinarith [Nat.cast_nonneg (α:=ℝ) M]
    positivity))

#print axioms odd_step_le_tail_difference
#print axioms odd_tail_finite_prefix
end OpenMathResearch.LongCycleExcedances
