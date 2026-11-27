import SharpLagBudget
import ColorLoadGrid
import UniformLagBudget

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

abbrev ScaledBinomialAtom :=
  ∀ {A B N : ℕ}, 0 < A → 0 < B → A+B=N → ∀ {u v : ℝ}, 0 < u → 0 < v →
    2*√(A:ℝ)*√(B:ℝ)*(N.choose A:ℝ)*(u^A*v^B) ≤ √(N:ℝ)*(u+v)^N

theorem color_load_grid_mass_sharp (atom : ScaledBinomialAtom)
    {N d p : ℕ} (hd : 150 ≤ d) (half : 2*d ≤ N) (hp : 0 < p) :
    (∑ j ∈ range (p+1), colorLoad N d ((j:ℝ)/p)) ≤ (p:ℝ)/((N:ℝ)+1)+29/500 := by
  have hd0 : 0 < d := by omega
  have hdN : d < N := by omega
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  let u := (d:ℝ)/(N:ℝ)
  let v := 1-u
  have hu : 0 < u := div_pos (Nat.cast_pos.mpr hd0) hN
  have hv : 0 < v := sub_pos.mpr ((div_lt_one hN).mpr (Nat.cast_lt.mpr hdN))
  have hunit : u+v = 1 := by dsimp [v]; ring
  have hs := atom hd0 (Nat.sub_pos_of_lt hdN) (show d+(N-d)=N by omega) hu hv
  rw [hunit, one_pow, mul_one, Nat.cast_sub hdN.le] at hs
  apply color_load_grid_mass hp hd0 hdN
  apply modal_bound_two_grids (show (150:ℝ) ≤ d by exact_mod_cast hd)
    (show (2:ℝ)*d ≤ N by exact_mod_cast half)
  convert hs using 1
  simp only [colorLoad, v]
  ring

/-- The same envelope applies to the actual colorLoad grids at n and n−1. -/
theorem two_color_load_grids_mass (atom : ScaledBinomialAtom)
    {n d p : ℕ} (hd : 150 ≤ d) (half : 2*d ≤ n-1) (hp : 0 < p) :
    (∑ j ∈ range (p+1), colorLoad n d ((j:ℝ)/p)) ≤ (p:ℝ)/n+29/500 ∧
    (∑ j ∈ range (p+1), colorLoad (n-1) d ((j:ℝ)/p)) ≤ (p:ℝ)/n+29/500 := by
  have hn : 0 < n := by omega
  have h0 := color_load_grid_mass_sharp atom hd (by omega : 2*d ≤ n) hp
  have h1 := color_load_grid_mass_sharp atom hd half hp
  rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at h1
  have hmono : (p:ℝ)/((n:ℝ)+1) ≤ (p:ℝ)/n :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg p) (Nat.cast_pos.mpr hn) (by linarith)
  exact ⟨h0.trans (add_le_add hmono le_rfl), h1⟩

theorem sharp_front_lag_of_two_color_grids (atom : ScaledBinomialAtom)
    {n k p : ℕ} {L α : ℝ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hp : 0 < p) (hrank : 4*p^2 ≤ n)
    (hhalf : 2*(k-1) ≤ n-1)
    (hL : L ≤ ∑ j ∈ range (p+1), colorLoad n (k-1) ((j:ℝ)/p))
    (hres : ((k:ℝ)*p/n)*L ≤ (151/100)*
      ∑ j ∈ range (p+1), colorLoad (n-1) (k-1) ((j:ℝ)/p))
    (hα : (99:ℝ)/(100*(1+(8/3)*((k:ℝ)*p/n))) ≤ α) :
    L < (8/25)*α := by
  let a := (k:ℝ)*p/n
  have ha : 0 ≤ a := by positivity
  have hs := front_grid_scale hn hrank
  have hsR : 200*(p:ℝ) ≤ n := by exact_mod_cast hs
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hpn : (p:ℝ)/n ≤ 1/200 := by
    apply (div_le_iff₀ hnR).mpr
    linarith
  have hα' : (99:ℝ)/100 ≤ (1+(8/3)*a)*α := by
    have h := (div_le_iff₀ (by positivity : 0 < 100*(1+(8/3)*a))).mp hα
    nlinarith only [h]
  by_cases hd : 150 ≤ k-1
  · obtain ⟨h0, h1⟩ := two_color_load_grids_mass atom hd hhalf hp
    have hmesh : (p:ℝ)/n+29/500 ≤ 1/200+29/500 := add_le_add hpn le_rfl
    exact two_grid_relative_lag ha hα'
      (hL.trans (h0.trans hmesh))
      (hres.trans (mul_le_mul_of_nonneg_left (h1.trans hmesh) (by norm_num)))
  · have hkR : (k:ℝ) ≤ 150 := by exact_mod_cast (show k ≤ 150 by omega)
    have ha' : a ≤ 3/4 := by
      dsimp [a]
      rw [mul_div_assoc]
      calc
        (k:ℝ)*((p:ℝ)/n) ≤ 150*(1/200) :=
          mul_le_mul hkR hpn (by positivity) (by norm_num)
        _ = _ := by norm_num
    have hsmall := hL.trans (small_lag_grid_mass hp hk hkn hs ha')
    have hres' : a*L ≤ a*(1/500) := mul_le_mul_of_nonneg_left hsmall ha
    exact two_grid_relative_lag ha hα' (hsmall.trans (by norm_num))
      (by nlinarith only [hres',ha'])

#print axioms color_load_grid_mass_sharp
#print axioms two_color_load_grids_mass
#print axioms sharp_front_lag_of_two_color_grids
end OpenMathResearch.LongCycleExcedances
