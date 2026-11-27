import PairedPoleConvergence

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Filter
open scoped PowerSeries Topology

/-- Finite powers preserve coefficientwise convergence without needing a
topology on formal power series. -/
theorem tendsto_power_coeff_of_tendsto_coeff {ι : Type*} {l : Filter ι}
    {F : ι → ℂ⟦X⟧} {G : ℂ⟦X⟧}
    (hF : ∀ n, Tendsto (fun i => PowerSeries.coeff (R := ℂ) n (F i)) l
      (𝓝 (PowerSeries.coeff (R := ℂ) n G))) (j n : ℕ) :
    Tendsto (fun i => PowerSeries.coeff (R := ℂ) n (F i ^ j)) l
      (𝓝 (PowerSeries.coeff (R := ℂ) n (G ^ j))) := by
  induction j generalizing n with
  | zero => simpa only [pow_zero] using (tendsto_const_nhds : Tendsto
      (fun _ : ι => PowerSeries.coeff (R := ℂ) n 1) l (𝓝 (PowerSeries.coeff (R := ℂ) n 1)))
  | succ j ih =>
    simp only [pow_succ, PowerSeries.coeff_mul]
    exact tendsto_finsetSum _ fun a _ => (ih a.1).mul (hF a.2)

/-- The fixed coefficient of any power of the finite pole logarithm
converges to the corresponding power of its coefficientwise limit. -/
theorem tendsto_paired_log_power_coeff (C : ℝ) {S : ℝ} (hS : S ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (j n : ℕ) :
    Tendsto (fun A : Finset ℤ => PowerSeries.coeff (R := ℂ) n
      ((∑ q ∈ A, pairedCycleLog k C S q) ^ j)) atTop
      (𝓝 (PowerSeries.coeff (R := ℂ) n
        ((PowerSeries.mk fun p => if k ≤ p then
          (∑' q : ℤ, ((pairedPoleDenom C S q)⁻¹)^p)/(p:ℂ) else 0) ^ j))) := by
  apply tendsto_power_coeff_of_tendsto_coeff
  intro p
  simpa only [HasSum, SummationFilter.unconditional, map_sum, PowerSeries.coeff_mk] using
    (hasSum_paired_cycle_log_coeff C hS hk p)

/-- Every truncated exponential coefficient is a continuous expression
in its logarithm coefficients, because the outer sum is finite. -/
theorem tendsto_truncated_exp_coeff {ι : Type*} {l : Filter ι}
    {F : ι → ℂ⟦X⟧} {G : ℂ⟦X⟧}
    (hF : ∀ n, Tendsto (fun i => PowerSeries.coeff (R := ℂ) n (F i)) l
      (𝓝 (PowerSeries.coeff (R := ℂ) n G))) (H n : ℕ) :
    Tendsto (fun i => ∑ j ∈ Finset.range (H+1),
      PowerSeries.coeff (R := ℂ) n (F i ^ j) / (j.factorial:ℂ)) l
      (𝓝 (∑ j ∈ Finset.range (H+1),
        PowerSeries.coeff (R := ℂ) n (G ^ j) / (j.factorial:ℂ))) := by
  apply tendsto_finsetSum
  intro j _
  simpa only [div_eq_mul_inv] using
    (tendsto_power_coeff_of_tendsto_coeff hF j n).mul_const ((j.factorial:ℂ)⁻¹)

#print axioms tendsto_truncated_exp_coeff
#print axioms tendsto_paired_log_power_coeff
#print axioms tendsto_power_coeff_of_tendsto_coeff
end OpenMathResearch.LongCycleExcedances
