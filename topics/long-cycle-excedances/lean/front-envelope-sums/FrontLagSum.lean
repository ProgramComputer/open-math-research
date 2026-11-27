import FrontEnvelopeSum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial

theorem front_norm_old_full (P : ℝ[X]) {h : ℕ} {a u : ℝ}
    (ha : 0 < a) (hu : 0 < u)
    (hold : frontCoefficientNorm (frontOldResidual P h a u) h (7/8*u) (9/8*u) ≤ a/10) :
    frontCoefficientNorm P h (7/8*u) (9/8*u) ≤ (1+9/8+1/10)*a := by
  let T := frontOldResidual P h a u
  let L := 7/8*u
  let U := 9/8*u
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have he : P = T + (C a*X^h+C (a/u)*X^(h+1)) := by
    unfold T frontOldResidual
    rw [pow_succ, show a/u=a*(1/u) by ring, C_mul]
    ring
  have hT := front_norm_add_le T (C a*X^h+C (a/u)*X^(h+1)) h hL hU
  rw [←he] at hT
  have hC := front_norm_add_le (C a*X^h) (C (a/u)*X^(h+1)) h hL hU
  rw [front_norm_monomial,front_norm_monomial,abs_of_pos ha,abs_of_pos (div_pos ha hu)] at hC
  have h1 : frontCoefficientWeight h L U h = 1 := by simp [frontCoefficientWeight]
  have h2 : frontCoefficientWeight h L U (h+1) = U := by simp [frontCoefficientWeight]
  rw [h1,h2] at hC
  have hsc : (a/u)*U = 9/8*a := by dsimp [U]; field_simp [hu.ne'] <;> ring
  rw [hsc] at hC
  change frontCoefficientNorm T h L U ≤ a/10 at hold
  linarith

/-- A finite weighted lag bound from the near coefficient ratio and a
geometric far envelope beginning at distance two from the upper center. -/
theorem front_norm_lag (P V : ℝ[X]) {h J : ℕ} {a L U : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hU : 0 ≤ U) (hJ : h+2 ≤ J)
    (hP : frontCoefficientNorm P h L U ≤ (1+9/8+1/10)*a)
    (hnear : ∀ j ≤ J, |V.coeff j| * frontCoefficientWeight h L U j ≤
      (8/25)*(|P.coeff j| * frontCoefficientWeight h L U j))
    (hfar : ∀ j, J < j → |V.coeff j| * frontCoefficientWeight h L U j ≤
      (36*a)*(1/75)^(j-(h+1))) :
    frontCoefficientNorm V h L U < 18/25*a := by
  let t (j : ℕ) := |V.coeff j| * frontCoefficientWeight h L U j
  let p (j : ℕ) := |P.coeff j| * frontCoefficientWeight h L U j
  let s₀ := V.support.filter (fun j => j ≤ J)
  let s₁ := V.support.filter (fun j => ¬ j ≤ J)
  have hsum : (∑ j ∈ s₀, t j) + (∑ j ∈ s₁, t j) = frontCoefficientNorm V h L U :=
    sum_filter_add_sum_filter_not _ _ _
  have hp (j : ℕ) : 0 ≤ p j := by
    unfold p frontCoefficientWeight
    split <;> positivity
  have he : (∑ j ∈ s₀, p j) = ∑ j ∈ s₀ ∩ P.support, p j := by
    symm
    apply sum_subset inter_subset_left
    intro j hj hj'
    have hnot : j ∉ P.support := fun h => hj' (mem_inter.mpr ⟨hj,h⟩)
    have hz : P.coeff j = 0 := by
      by_contra h
      exact hnot (mem_support_iff.mpr h)
    simp [p,hz]
  have hp' : (∑ j ∈ s₀, p j) ≤ frontCoefficientNorm P h L U := by
    rw [he]
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun j _ _ => hp j)
  have hn : (∑ j ∈ s₀, t j) ≤ (8/25)*(1+9/8+1/10)*a := by
    calc
      _ ≤ ∑ j ∈ s₀, (8/25)*p j := sum_le_sum (fun j hj => hnear j (mem_filter.mp hj).2)
      _ = (8/25)*(∑ j ∈ s₀, p j) := (mul_sum ..).symm
      _ ≤ (8/25)*((1+9/8+1/10)*a) := mul_le_mul_of_nonneg_left (hp'.trans hP) (by norm_num)
      _ = _ := by ring
  have hf := front_finite_geometric_bound s₁ (1/75) (36*a) 2 (by norm_num) (by norm_num)
    (by positivity) (·-(h+1))
    (fun j hj => by change 2 ≤ j-(h+1); have := (mem_filter.mp hj).2; omega)
    (fun j hj k hk he => by
      change j-(h+1)=k-(h+1) at he
      have := (mem_filter.mp hj).2
      have := (mem_filter.mp hk).2
      omega)
    t (fun j hj => hfar j (by have := (mem_filter.mp hj).2; omega))
  rw [←hsum]
  norm_num at hn hf ⊢
  linarith only [hn,hf,ha]

/-- Any finite rows satisfying the per-index envelopes give the two strict
coefficient tests with the explicit multiplier furnished by insertion. -/
theorem front_certificates_of_weighted_envelopes (P Q V : ℝ[X]) {h J : ℕ} {a u n : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hcap : (9/8:ℝ)*u ≤ 1/2) (hJ : h+2 ≤ J)
    (hc : P.coeff h = a) (hc' : P.coeff (h+1)=a/u)
    (hrec : Q = C n*X*P+(1-X)*(X*P.derivative)+V)
    (hleft : ∀ j < h, |P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (51/10*a)*(((h-j:ℕ):ℝ)+1)*(1/300)^ (h-j))
    (hright : ∀ j, h+1 < j → |P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (9*a)*(((j-(h+1):ℕ):ℝ)+1)*(1/300)^(j-(h+1)))
    (hnear : ∀ j ≤ J, |V.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (8/25)*(|P.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j))
    (hfar : ∀ j, J < j → |V.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
      (36*a)*((j-(h+1):ℕ):ℝ)*(((j-(h+1):ℕ):ℝ)+1)*(1/300)^(j-(h+1))) :
    frontCoefficientNorm (frontOldResidual P h a u) h (7/8*u) (9/8*u) < a/8 ∧
    frontCoefficientNorm (frontNextResidual P Q (C n*X+(1-X)*C ((h:ℝ)+1)) h a)
      h (7/8*u) (9/8*u) < a := by
  obtain ⟨hold,hD⟩ := front_old_and_centered_norm P ha hc hc' hleft hright
  have hP := front_norm_old_full P ha hu hold.le
  have hL : 0 < (7/8:ℝ)*u := by positivity
  have hU : 0 ≤ (9/8:ℝ)*u := by positivity
  have hf (j : ℕ) (hj : J < j) :
      |V.coeff j| * frontCoefficientWeight h (7/8*u) (9/8*u) j ≤
        (36*a)*(1/75)^(j-(h+1)) := by
    let l := j-(h+1)
    have hl : 1 ≤ l := by dsimp [l]; omega
    have hq := front_quadratic_rank_bound hl
    have hq' : (l:ℝ)*((l:ℝ)+1) ≤ 4^l := by linarith only [hq, pow_nonneg (by norm_num : (0:ℝ) ≤ 4) l]
    apply (hfar j hj).trans
    change 36*a*(l:ℝ)*((l:ℝ)+1)*(1/300)^l ≤ 36*a*(1/75)^l
    rw [show (1/75:ℝ)=4*(1/300) by norm_num, mul_pow]
    calc
      _ = (36*a)*((l:ℝ)*((l:ℝ)+1)*(1/300)^l) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hq' (by positivity)) (by positivity)
  have hV := front_norm_lag P V ha hL hU hJ hP hnear hf
  refine ⟨hold.trans (by linarith),?_⟩
  rw [front_next_residual_eq P Q V h a n hrec]
  exact front_norm_closed_successor (frontCenteredDerivative P h a) V hL
    (by linarith) hcap ha hD.le hV.le

#print axioms front_certificates_of_weighted_envelopes
#print axioms front_norm_old_full
#print axioms front_norm_lag
end OpenMathResearch.LongCycleExcedances
