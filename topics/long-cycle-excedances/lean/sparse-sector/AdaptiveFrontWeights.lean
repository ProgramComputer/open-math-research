import AdaptiveFrontBounds

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Absorb both adaptive endpoint multipliers into the common geometric ratio. -/
theorem front_adaptive_multipliers {n h : ℕ} (hn : 10000 ≤ n) (hh : 0 < h)
    (hH : h ≤ ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊) {ρ : ℝ}
    (hup : ρ ≤ (51/10)*(((h:ℝ)+1)/h)) (hinv : 1/ρ ≤ 51/10) :
    (8/7:ℝ)*(1/ρ)*frontInverseGrowth n h ≤ 1/300 ∧
      (9/8:ℝ)*ρ*frontInverseGrowth n h ≤ 1/300 := by
  let q := frontInverseGrowth n h
  have hq : 0 < q := front_inverse_growth_pos n hh
  have hp : (0:ℝ)<h := by exact_mod_cast hh
  have coarse : (((h:ℝ)+1)/h) ≤ 2 := (div_le_iff₀ hp).mpr (by
    have he : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith only [he])
  have combine (R Q : ℝ) (hR : 0 ≤ R) (hqQ : q ≤ Q) (hC : ρ ≤ R) (hI : 1/ρ ≤ R)
      (hL : (8/7:ℝ)*R*Q ≤ 1/300) (hU : (9/8:ℝ)*R*Q ≤ 1/300) :
      (8/7:ℝ)*(1/ρ)*q ≤ 1/300 ∧ (9/8:ℝ)*ρ*q ≤ 1/300 := by
    constructor
    · exact (mul_le_mul (mul_le_mul_of_nonneg_left hI (by norm_num)) hqQ hq.le
        (by positivity : (0:ℝ) ≤ (8/7)*R)).trans hL
    · exact (mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num)) hqQ hq.le
        (by positivity : (0:ℝ) ≤ (9/8)*R)).trans hU
  by_cases h5 : h ≤ 5
  · have hsmall := front_inverse_growth_small_rank hn hh h5
    apply combine (51/5) (1/4000) (by norm_num) hsmall _ (hinv.trans (by norm_num))
      (by norm_num) (by norm_num)
    exact hup.trans (by linarith only [coarse])
  · have h6 : (6:ℝ) ≤ h := by exact_mod_cast (show 6 ≤ h by omega)
    have hfine : (((h:ℝ)+1)/h) ≤ 7/6 := (div_le_iff₀ hp).mpr (by linarith only [h6])
    have hbig := front_inverse_growth_bound hn hh hH
    apply combine 6 (1/2200) (by norm_num) hbig _ (hinv.trans (by norm_num))
      (by norm_num) (by norm_num)
    exact hup.trans (by linarith only [hfine])

/-- The two far-rank comparisons needed for the old-row and insertion tails. -/
theorem front_far_rank_geometry {n h j : ℕ} (hn : 10000 ≤ n)
    (hH : h ≤ ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊) (hj : ⌊sqrt (n:ℝ)/2⌋₊ < j) :
    h+1 < j ∧ ((h:ℝ)+1) < (18/7)*((j-(h+1):ℕ):ℝ) ∧
      (j:ℝ) < 4*((j-(h+1):ℕ):ℝ) := by
  let y := sqrt (n:ℝ)
  have hy : (100:ℝ) ≤ y := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    norm_num
    exact_mod_cast hn
  have hh : (h:ℝ) ≤ (7/20:ℝ)*y := by
    have hfloor := (Nat.floor_le (show 0≤(7/20:ℝ)*y by positivity))
    exact (show (h:ℝ) ≤ ((⌊(7/20:ℝ)*y⌋₊:ℕ):ℝ) by exact_mod_cast hH).trans hfloor
  have hj' : y/2 < (j:ℝ) := (Nat.floor_lt (by positivity)).mp hj
  have hlim : (h:ℝ)+1 ≤ (9/25:ℝ)*y := by linarith only [hh,hy]
  have hi : h+1 < j := by
    have he : ((h:ℝ)+1) < (j:ℝ) := by linarith only [hj',hlim,hy]
    exact_mod_cast he
  refine ⟨hi, ?_, ?_⟩
  all_goals
    rw [Nat.cast_sub hi.le,Nat.cast_add,Nat.cast_one]
    linarith only [hj',hlim,hy]

theorem front_far_reciprocal {d b ℓ : ℝ} (hb : 0 ≤ b) (hl : 0 ≤ ℓ)
    (hlim : b ≤ (18/7)*ℓ) (hd : 99/(100*(1+(8/3:ℝ)*b)) ≤ d) :
    1/d ≤ 8*(ℓ+1) := by
  have hp : 0 < 100*(1+(8/3:ℝ)*b) := by positivity
  have hd0 := (div_pos (by norm_num) hp).trans_le hd
  have h := (div_le_iff₀ hp).mp hd
  apply (div_le_iff₀ hd0).mpr
  have hb' : 100*(1+(8/3:ℝ)*b) ≤ 99*(8*(ℓ+1)) := by linarith only [hlim,hl]
  have hc := mul_le_mul_of_nonneg_left hb' hd0.le
  nlinarith only [h,hc]

/-- The bare right weight after factoring out the exact upper central term. -/
theorem front_bare_right_weight {n h j : ℕ} (hh : 0 < h) (hj : h+1 ≤ j)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hU : (9/8:ℝ)*ρ*frontInverseGrowth n h ≤ 1/300) :
    let u := ρ*((h:ℝ)/((h:ℝ)+1))^n
    (j:ℝ)^n*((9/8:ℝ)*u)^(j-(h+1)) ≤ (((h:ℝ)+1)^n)*(1/300)^(j-(h+1)) := by
  let H : ℝ := (h:ℝ)+1
  let l := j-(h+1)
  let r : ℝ := (h:ℝ)/H
  let B : ℝ := (9/8)*ρ
  have hH : 0 < H := by dsimp [H]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hb := pow_le_pow_left₀ (show 0 ≤ ((j:ℝ)/H)*r^l by positivity)
    (front_right_bare_ratio hj) n
  change (j:ℝ)^n*((9/8:ℝ)*(ρ*r^n))^l ≤ H^n*(1/300)^l
  rw [←mul_assoc]
  change (j:ℝ)^n*(B*(r^n))^l ≤ H^n*(1/300)^l
  have he : (j:ℝ)^n = H^n*((j:ℝ)/H)^n := by
    rw [←mul_pow, mul_comm H, div_mul_cancel₀ _ hH.ne']
  have hbare : (((j:ℝ)/H)*r^l)^n * B^l ≤ (1/300:ℝ)^l := by
    calc
      _ ≤ (((1-1/H^2)^l)^n) * B^l := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (B*frontInverseGrowth n h)^l := by
        have hq : ((1-1/H^2)^l)^n = (frontInverseGrowth n h)^l := pow_right_comm _ _ _
        rw [hq, mul_pow B (frontInverseGrowth n h) l]
        exact mul_comm ((frontInverseGrowth n h)^l) (B^l)
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hB.le (front_inverse_growth_pos n hh).le) hU l
  rw [he,mul_pow B (r^n) l,pow_right_comm r n l]
  rw [show H^n*((j:ℝ)/H)^n*(B^l*(r^l)^n) = H^n*((((j:ℝ)/H)*r^l)^n*B^l) by rw [mul_pow ((j:ℝ)/H) (r^l) n]; ring]
  exact mul_le_mul_of_nonneg_left hbare (by positivity)

/-- The bare left weight after removing the exact lower central term. -/
theorem front_bare_left_weight {n h j : ℕ} (hh : 0 < h) (hj : j ≤ h)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hL : (8/7:ℝ)*(1/ρ)*frontInverseGrowth n h ≤ 1/300) :
    let u := ρ*((h:ℝ)/((h:ℝ)+1))^n
    (j:ℝ)^n/((7/8:ℝ)*u)^(h-j) ≤ (h:ℝ)^n*(1/300)^(h-j) := by
  let H : ℝ := h
  let l := h-j
  let r : ℝ := (H+1)/H
  let B : ℝ := (8/7)*(1/ρ)
  have hH : 0 < H := by dsimp [H]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hb := pow_le_pow_left₀ (show 0 ≤ ((j:ℝ)/H)*r^l by positivity)
    (front_left_bare_ratio hh hj) n
  let u := ρ*((h:ℝ)/((h:ℝ)+1))^n
  have hInv : 1/((7/8:ℝ)*u) = B*r^n := by
    dsimp only [u,B,r,H]
    rw [div_pow,div_pow]
    field_simp [hρ.ne',hH.ne',show (h:ℝ)+1 ≠ 0 by positivity] <;> ring
  have he : (j:ℝ)^n = H^n*((j:ℝ)/H)^n := by
    rw [←mul_pow, mul_comm H, div_mul_cancel₀ _ hH.ne']
  have hbare : (((j:ℝ)/H)*r^l)^n * B^l ≤ (1/300:ℝ)^l := by
    calc
      _ ≤ (((1-1/((h:ℝ)+1)^2)^l)^n) * B^l := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (B*frontInverseGrowth n h)^l := by
        have hq : ((1-1/((h:ℝ)+1)^2)^l)^n = (frontInverseGrowth n h)^l := pow_right_comm _ _ _
        rw [hq, mul_pow B (frontInverseGrowth n h) l]
        exact mul_comm ((frontInverseGrowth n h)^l) (B^l)
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hB.le (front_inverse_growth_pos n hh).le) hL l
  change (j:ℝ)^n/((7/8:ℝ)*u)^l ≤ H^n*(1/300)^l
  rw [one_div] at hInv
  rw [div_eq_mul_inv,←inv_pow,hInv,he,mul_pow B (r^n) l,pow_right_comm r n l]
  rw [show H^n*((j:ℝ)/H)^n*(B^l*(r^l)^n) = H^n*((((j:ℝ)/H)*r^l)^n*B^l) by rw [mul_pow ((j:ℝ)/H) (r^l) n]; ring]
  exact mul_le_mul_of_nonneg_left hbare (by positivity)

#print axioms front_adaptive_multipliers
#print axioms front_far_rank_geometry
#print axioms front_far_reciprocal
#print axioms front_bare_right_weight
#print axioms front_bare_left_weight
end OpenMathResearch.LongCycleExcedances
