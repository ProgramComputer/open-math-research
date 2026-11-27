import FourierGeometricRemainder

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Real

theorem disk_geometric_remainder_bound {ι : Type*} (P : ι → ℂ) {ρ r : ℝ}
    (hρ : 0 ≤ ρ) (hr : ρ < r) (hp : ∀ i, r ≤ ‖P i‖)
    (hs : Summable (fun i => 1 / ‖P i‖^2)) (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    let q := ρ/r
    ‖∑' i, z^(m+1)/(P i^(m+1)*(P i-z))‖ ≤ q^m*(ρ/(1-q))*(∑' i, 1/‖P i‖^2) := by
  let q := ρ/r
  have hr0 := hρ.trans_lt hr
  have hq0 : 0 ≤ q := div_nonneg hρ hr0.le
  have hq1 : q < 1 := (div_lt_one hr0).mpr hr
  have hqpos : 0 < 1-q := sub_pos.mpr hq1
  let C := q^m*(ρ/(1-q))
  have hbound (i : ι) : ‖z^(m+1)/(P i^(m+1)*(P i-z))‖ ≤ C*(1/‖P i‖^2) := by
    have hpi := hr0.trans_le (hp i)
    have hzP : ‖z‖ ≤ q*‖P i‖ := calc
      _ ≤ ρ := hz
      _ = q*r := (div_mul_cancel₀ _ hr0.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hp i) hq0
    have hdiff : (1-q)*‖P i‖ ≤ ‖P i-z‖ := by nlinarith [norm_sub_norm_le (P i) z]
    have hsep : 0 < ‖P i-z‖ := (mul_pos hqpos hpi).trans_le hdiff
    have he : ‖z‖/(‖P i‖*‖P i-z‖) ≤ (ρ/(1-q)) * (1/‖P i‖^2) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos hpi hsep) (mul_pos hqpos (sq_pos_of_pos hpi))]
      calc
        _ ≤ ρ*((1-q)*‖P i‖^2) := mul_le_mul_of_nonneg_right hz (by positivity)
        _ ≤ _ := by
          have hd := mul_le_mul_of_nonneg_left hdiff (mul_nonneg hρ hpi.le)
          nlinarith only [hd]
    have hpow := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hpi.le) ((div_le_iff₀ hpi).mpr hzP) m
    calc
      _ = (‖z‖/‖P i‖)^m * (‖z‖/(‖P i‖*‖P i-z‖)) := by
        rw [norm_div,norm_mul,norm_pow,norm_pow,pow_succ,pow_succ,div_pow]
        field_simp
        exact Or.inl (by ring)
      _ ≤ q^m*((ρ/(1-q))*(1/‖P i‖^2)) :=
        mul_le_mul hpow he (by positivity) (pow_nonneg hq0 _)
      _ = _ := by dsimp only [C]; ring
  have hdom := hs.mul_left C
  have hs' := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hdom
  exact (norm_tsum_le_tsum_norm hs').trans ((hs'.tsum_le_tsum hbound hdom).trans_eq (by rw [tsum_mul_left]))

#print axioms disk_geometric_remainder_bound
end OpenMathResearch.LongCycleExcedances
