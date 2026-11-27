import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

/-- Physical denominator gaps stay small even at arbitrarily large aspect:
one power of the chosen radius gap controls the growth in the aspect. -/
theorem selected_gap_is_small {x K r : ℝ} (hx : 44 ≤ x) (hk : 100 ≤ K) (hr : 0 < r)
    (hu : 1 ≤ x*(K*(π/r)^2)) :
    let c := min (1/25 : ℝ) (4/x)
    (49/100)*(c*r/K) ≤ 1/16 := by
  let c := min (1/25 : ℝ) (4/x)
  have hx0 : 0 < x := by linarith
  have hK : 0 < K := by linarith
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hcle : c ≤ 1/25 := min_le_left _ _
  have hcx : c*x ≤ 4 := (le_div_iff₀ hx0).mp (min_le_right _ _)
  have hrs : r^2 ≤ x*(K*π^2) := by
    rwa [div_pow,←mul_div_assoc,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),one_mul] at hu
  have hp2 : π^2 ≤ (315/100)^2 := pow_le_pow_left₀ Real.pi_pos.le (by linarith [Real.pi_lt_d2]) _
  have hcx2 : c^2*x ≤ 4/25 := calc
    _ = c*(c*x) := by ring
    _ ≤ c*4 := mul_le_mul_of_nonneg_left hcx hc.le
    _ ≤ _ := by linarith
  have hbound : (c*r)^2 ≤ (4/25)*(315/100)^2*K := calc
    _ = c^2*r^2 := by ring
    _ ≤ c^2*(x*(K*π^2)) := mul_le_mul_of_nonneg_left hrs (sq_nonneg c)
    _ = (c^2*x)*π^2*K := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul hcx2 hp2 (sq_nonneg _) (by norm_num)) hK.le
  have hKK := mul_le_mul_of_nonneg_right hk hK.le
  change 49/100*(c*r/K) ≤ 1/16
  rw [←mul_div_assoc,div_le_iff₀ hK]
  have h1 : (49/100*(c*r))^2 ≤ (1/16*K)^2 := by nlinarith only [hbound,hKK]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp h1

/-- Radius movement at most twice the principal scale gives the dimensionless
factor used on the same circle in both Fourier coefficient estimates. -/
theorem selected_ratio_factor {c q Δ : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hΔ : Δ ≤ 2*q) (hδ : (49/100)*(c*q) ≤ 1/16) :
    let δ := (49/100)*(c*q)
    1+Δ*(1+δ)/δ ≤ 1+(425/98)/c := by
  let δ := (49/100)*(c*q)
  have hd : 0 < δ := by dsimp [δ]; positivity
  apply add_le_add_right
  apply (div_le_div_iff₀ hd hc).mpr
  calc
    _ ≤ (2*q)*(1+δ)*c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΔ (by linarith)) hc.le
    _ ≤ (2*q)*(1+1/16)*c := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_right hδ 1) (by positivity)) hc.le
    _ = _ := by dsimp [δ]; ring

/-- The selected-circle factor is at most 110 throughout the bounded interval
and at most eleven tenths of the aspect thereafter. -/
theorem selected_ratio_regimes {x : ℝ} (hx : 44 ≤ x) :
    let c := min (1/25 : ℝ) (4/x)
    (x ≤ 100 → 1+(425/98)/c ≤ 110) ∧
    (100 ≤ x → 1+(425/98)/c ≤ (11/10)*x) := by
  have hx0 : 0 < x := by linarith
  constructor
  · intro h
    rw [min_eq_left ((le_div_iff₀ hx0).mpr (by linarith))]
    norm_num
  · intro h
    rw [min_eq_right ((div_le_iff₀ hx0).mpr (by linarith)),div_div_eq_mul_div]
    linarith

/-- Uniform numerical forms of the selected-circle quotient prefactor.
The large-aspect power is three halves. -/
theorem selected_amplitude_regimes {x K r : ℝ} (hx : 44 ≤ x) (hk : 100 ≤ K) (hr : 0 < r)
    (hu : 1 ≤ x*(K*(π/r)^2)) :
    let c := min (1/25 : ℝ) (4/x)
    (x ≤ 100 → (2+r/K)*(1+(425/98)/c) ≤ 567) ∧
    (100 ≤ x → (2+r/K)*(1+(425/98)/c) ≤ (57/100)*x*Real.sqrt x) := by
  let c := min (1/25 : ℝ) (4/x)
  have hx0 : 0 < x := by linarith
  have hK : 0 < K := by linarith
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hs := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  have hrs : r^2 ≤ x*(K*π^2) := by
    rwa [div_pow,←mul_div_assoc,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),one_mul] at hu
  have hn : π^2 ≤ (315/100)^2 := pow_le_pow_left₀ Real.pi_pos.le (by linarith [Real.pi_lt_d2]) _
  have hq : r/K ≤ (315/1000)*Real.sqrt x := by
    apply (div_le_iff₀ hK).mpr
    apply (sq_le_sq₀ hr.le (by positivity)).mp
    calc
      _ ≤ x*(K*π^2) := hrs
      _ ≤ x*(K*(315/100)^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hK.le) hx0.le
      _ ≤ x*K^2*(315/1000)^2 := by
        have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk hK.le) hx0.le
        nlinarith only [hh]
      _ = _ := by nth_rw 1 [← hs]; ring
  obtain ⟨hB,hL⟩ := selected_ratio_regimes hx
  have hF : 0 ≤ 1+(425/98)/c := by positivity
  constructor
  · intro h
    have h10 : Real.sqrt x ≤ 10 := (sq_le_sq₀ hs0 (by norm_num)).mp (by nlinarith only [h,hs])
    change (2+r/K)*(1+(425/98)/c) ≤ _
    calc
      _ ≤ (2+315/100)*110 := mul_le_mul (by linarith) (hB h) hF (by norm_num)
      _ ≤ _ := by norm_num
  · intro h
    have h10 : 10 ≤ Real.sqrt x := (sq_le_sq₀ (by norm_num) hs0).mp (by nlinarith only [h,hs])
    calc
      _ ≤ ((515/1000)*Real.sqrt x)*((11/10)*x) :=
        mul_le_mul (by linarith) (hL h) hF (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg hx0.le hs0]

#print axioms selected_amplitude_regimes
#print axioms selected_ratio_regimes
#print axioms selected_gap_is_small
#print axioms selected_ratio_factor
end OpenMathResearch.LongCycleExcedances
