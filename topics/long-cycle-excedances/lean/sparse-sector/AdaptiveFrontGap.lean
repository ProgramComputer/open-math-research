import AdaptiveFrontWeights
import RealFront

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Neighboring adaptive centers differ by more than the factor used to
separate their two coefficient boxes. -/
theorem adaptive_front_adjacent_gap {n h : ℕ} (hn : 10000 ≤ n) (hh : 0 < h)
    (hH : h ≤ ⌊(7/20:ℝ)*sqrt (n:ℝ)⌋₊) {ρ σ : ℝ}
    (hr : 0 < ρ) (hrMax : ρ ≤ 51/5) (hsMin : 1 ≤ (51/5:ℝ)*σ) :
    let u := ρ*((h:ℝ)/((h:ℝ)+1))^n
    let v := σ*(((h:ℝ)+1)/((h:ℝ)+2))^n
    20*u < v := by
  let u := ρ*((h:ℝ)/((h:ℝ)+1))^n
  let v := σ*(((h:ℝ)+1)/((h:ℝ)+2))^n
  let q := frontInverseGrowth n h
  have hpos : 0 < u := mul_pos hr (by positivity)
  have hq : 0 < q := front_inverse_growth_pos n hh
  have hqmax : q ≤ 1/2200 := front_inverse_growth_bound hn hh hH
  have hbare :
      q*(((h:ℝ)+1)/((h:ℝ)+2))^n = ((h:ℝ)/((h:ℝ)+1))^n := by
    unfold q frontInverseGrowth
    rw [←mul_pow]
    congr 1
    have h1 : (h:ℝ)+1 ≠ 0 := by positivity
    have h2 : (h:ℝ)+2 ≠ 0 := by positivity
    field_simp [h1,h2] <;> ring
  have he : ρ*q*v = σ*u := by
    change ρ * q * (σ*(((h:ℝ)+1)/((h:ℝ)+2))^n) = σ*(ρ*((h:ℝ)/((h:ℝ)+1))^n)
    rw [show ρ*q*(σ*(((h:ℝ)+1)/((h:ℝ)+2))^n) =
      σ*ρ*(q*(((h:ℝ)+1)/((h:ℝ)+2))^n) by ring,hbare]
    ring
  exact effective_front_adjacent_centers hpos hr hq hrMax hsMin hqmax he

/-- Combine the far weighted power estimate with a single polynomial rank
factor from the unweighted lag bound. -/
theorem front_far_weighted_lag {n j l : ℕ} {U t α c V : ℝ}
    (hU : 0 ≤ U) (ht : 0 ≤ t) (hα : 0 < α) (hV : 0 ≤ V)
    (hVupper : V ≤ (j:ℝ)^(n+1)) (hbare : (j:ℝ)^n*U^l ≤ t^n*(1/300)^l)
    (hrank : (j:ℝ) ≤ 4*(l:ℝ)) (hαrec : 1/α ≤ 8*((l:ℝ)+1))
    (hc : α*t^n*U = (9/8:ℝ)*c) :
    |V| * U^(l+1) ≤ (36*c)*(l:ℝ)*(((l:ℝ)+1))*(1/300)^l := by
  rw [abs_of_nonneg hV,pow_succ U l,←mul_assoc]
  have hn := mul_le_mul_of_nonneg_right hVupper (by positivity : 0 ≤ U^l)
  have hm := mul_le_mul_of_nonneg_left hbare (Nat.cast_nonneg (α:=ℝ) j)
  have h := (div_le_iff₀ hα).mp hαrec
  calc
    _ ≤ (((j:ℝ)^(n+1))*U^l)*U := mul_le_mul_of_nonneg_right hn hU
    _ = ((j:ℝ)*((j:ℝ)^n*U^l))*U := by rw [pow_succ (j:ℝ) n]; ring
    _ ≤ ((j:ℝ)*(t^n*(1/300)^l))*U := mul_le_mul_of_nonneg_right hm hU
    _ ≤ (4*(l:ℝ))*(t^n*(1/300)^l*U) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hrank (by positivity)
    _ ≤ (4*(l:ℝ))*((8*((l:ℝ)+1)*α)*(t^n*(1/300)^l*U)) := by
      have htU : 0 ≤ t^n*(1/300:ℝ)^l*U := by positivity
      have he := mul_le_mul_of_nonneg_right h htU
      rw [one_mul] at he
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = (32*(l:ℝ)*((l:ℝ)+1))*(α*t^n*U)*(1/300)^l := by ring
    _ = _ := by rw [hc] <;> ring

#print axioms adaptive_front_adjacent_gap
#print axioms front_far_weighted_lag
end OpenMathResearch.LongCycleExcedances
