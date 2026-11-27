import BinomialGridMesh
import BinomialColorLoad

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

/-- The grid estimate in the notation of the load proof.
Both endpoints vanish for an interior binomial outcome. -/
theorem color_load_grid_mass {n d p : ℕ} {M : ℝ} (hp : 0 < p)
    (hd : 0 < d) (hnd : d < n) (hpeak : colorLoad n d ((d:ℝ)/(n:ℝ)) ≤ M) :
    (∑ j ∈ range (p+1), colorLoad n d ((j:ℝ)/(p:ℝ))) ≤ (p:ℝ)/((n:ℝ)+1)+M := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hzero' : colorLoad n d (((0:ℕ):ℝ)/(p:ℝ)) = 0 := by
    simp [colorLoad, zero_pow hd.ne']
  have hlast : colorLoad n d ((p:ℝ)/(p:ℝ)) = 0 := by
    simp [colorLoad, div_self hpR.ne', zero_pow (Nat.sub_ne_zero_of_lt hnd)]
  have hset : Ico 1 p = (range p).erase 0 := by
    ext j
    simp
    omega
  rw [sum_range_succ, hlast, add_zero]
  have he := sum_erase_add (range p) (fun j : ℕ => colorLoad n d ((j:ℝ)/(p:ℝ)))
    (mem_range.mpr hp)
  simp only [hzero', add_zero] at he
  rw [←he, ←hset]
  have hpeak' : binomialDensity n d ((d:ℝ)/(n:ℝ)) ≤ M := by
    simpa only [binomialDensity, colorLoad, mul_comm ((n.choose d:ℕ):ℝ), mul_assoc] using hpeak
  convert binomial_grid_mass hp hd hnd hpeak' using 1
  apply sum_congr rfl
  intro i hi
  unfold colorLoad
  ring

#print axioms color_load_grid_mass
end OpenMathResearch.LongCycleExcedances
