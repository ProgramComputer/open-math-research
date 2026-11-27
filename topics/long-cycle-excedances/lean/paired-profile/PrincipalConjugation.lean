import SymmetricPoleComparison
import PrimitiveNumeratorInputs
import Mathlib.Algebra.Star.BigOperators

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Complex Real CycleProbability
open scoped PowerSeries ComplexConjugate

def reflectedPole (a : ℤ) : ℤ := -a-1

private theorem reflect_involutive (a : ℤ) : reflectedPole (reflectedPole a)=a := by
  unfold reflectedPole
  omega

theorem conjugate_pole_denom (C S : ℝ) (a : ℤ) :
    conj (pairedPoleDenom C S a)=pairedPoleDenom C S (reflectedPole a) := by
  have htwo : conj (2:ℂ)=2 := by rw [show (2:ℂ)=1+1 by norm_num,map_add,map_one]
  simp [pairedPoleDenom,reflectedPole,htwo]
  ring

theorem conjugate_primitive {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k)
    (C S : ℝ) (a q : ℤ) :
    PowerSeries.map conj (occupiedPrimitive k C S a q) =
      occupiedPrimitive k C S (reflectedPole a) (reflectedPole q) := by
  ext s
  have hb := (primitive_checker_numerator_inputs hd hk).1 s
  rw [PowerSeries.coeff_map]
  simp only [occupiedPrimitive,PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,hb]
  simp only [map_mul,map_div₀,map_sub,map_inv₀,map_pow,conjugate_pole_denom,
    Complex.conj_ofReal]

private theorem reflected_erased_window (M : ℕ) (a : ℤ) :
    ((symmetricPoleWindow M).erase a).image reflectedPole =
      (symmetricPoleWindow M).erase (reflectedPole a) := by
  ext q
  constructor
  · intro h
    obtain ⟨v,hv,rfl⟩ := mem_image.mp h
    have h := mem_erase.mp hv
    apply mem_erase.mpr
    exact ⟨fun he => h.1 (by simpa only [reflect_involutive] using congrArg reflectedPole he),
      (symmetric_pole_window_conjugate M v).mpr h.2⟩
  · intro h
    obtain ⟨ha,hq⟩ := mem_erase.mp h
    refine mem_image.mpr ⟨reflectedPole q,mem_erase.mpr ⟨?_,(symmetric_pole_window_conjugate M q).mpr hq⟩,
      reflect_involutive q⟩
    intro he
    exact ha (by simpa only [reflect_involutive] using congrArg reflectedPole he)

theorem conjugate_occupied_product {k : ℕ} {d : ℕ→ℝ} (hd : Spec k d) (hk : 2 ≤ k)
    (C S : ℝ) (M : ℕ) (a : ℤ) :
    PowerSeries.map conj (∏ q ∈ (symmetricPoleWindow M).erase a, (1+occupiedPrimitive k C S a q)) =
      ∏ q ∈ (symmetricPoleWindow M).erase (reflectedPole a), (1+occupiedPrimitive k C S (reflectedPole a) q) := by
  rw [map_prod,←reflected_erased_window M a,prod_image]
  · apply prod_congr rfl
    intro q _
    rw [map_add,map_one,conjugate_primitive hd hk]
  · intro p _ q _ hh
    simpa only [reflect_involutive] using congrArg reflectedPole hh

#print axioms conjugate_pole_denom
#print axioms conjugate_primitive
#print axioms conjugate_occupied_product
end OpenMathResearch.LongCycleExcedances
