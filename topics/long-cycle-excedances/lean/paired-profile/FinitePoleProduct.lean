import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped Polynomial PowerSeries

/-- Clearing all linear denominators gives the Lagrange partition of unity at
the reciprocal poles. -/
theorem finite_pole_partition {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (w : ι → K) (hne : s.Nonempty) (hinj : Set.InjOn w s)
    (hz : ∀ q ∈ s, w q ≠ 0) :
    (∑ a ∈ s, ∏ q ∈ s.erase a,
      Polynomial.C (w q/(w q-w a)) * (1-Polynomial.C (w q)⁻¹*Polynomial.X)) = (1 : K[X]) := by
  conv_rhs => rw [← Lagrange.sum_basis hinj hne]
  apply sum_congr rfl
  intro a ha
  rw [Lagrange.basis]
  apply prod_congr rfl
  intro q hq
  obtain ⟨hqa,hqs⟩ := mem_erase.mp hq
  have hne' : w q ≠ w a := fun h => hqa (hinj hqs ha h)
  have hc : w q/(w q-w a) = (w a-w q)⁻¹*(-w q) := by
    field_simp [sub_ne_zero.mpr hne', sub_ne_zero.mpr hne'.symm] <;> ring
  have hp : Polynomial.C (-w q)*(1-Polynomial.C (w q)⁻¹*Polynomial.X) =
      Polynomial.X-Polynomial.C (w q) := by
    rw [mul_sub,mul_one,←mul_assoc,←Polynomial.C_mul]
    rw [neg_mul,mul_inv_cancel₀ (hz q hqs)]
    simp only [map_neg, map_one]
    ring
  rw [Lagrange.basisDivisor, hc, Polynomial.C_mul, mul_assoc, hp]

/-- Exact finite occupied-pole factorization for arbitrary power-series
numerators. The actual factors can be D(u/w)-1 and their cleared numerators. -/
theorem finite_distinguished_pole_product {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (w : ι → K) (hne : s.Nonempty) (hinj : Set.InjOn w s)
    (hz : ∀ q ∈ s, w q ≠ 0) (g b : ι → K⟦X⟧)
    (hclear : ∀ q ∈ s, g q * (1-PowerSeries.C (R := K) (w q)⁻¹*PowerSeries.X) = b q) :
    ∏ q ∈ s, g q =
      ∑ a ∈ s, g a * ∏ q ∈ s.erase a, PowerSeries.C (R := K) (w q/(w q-w a))*b q := by
  have hpart : (∑ a ∈ s, ∏ q ∈ s.erase a,
      PowerSeries.C (R := K) (w q/(w q-w a)) * (1-PowerSeries.C (R := K) (w q)⁻¹*PowerSeries.X)) = 1 := by
    have h := congrArg Polynomial.coeToPowerSeries.ringHom (finite_pole_partition s w hne hinj hz)
    simpa only [map_sum, map_prod, map_mul, map_one, map_sub,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] using h
  calc
    _ = (∏ q ∈ s, g q) * (∑ a ∈ s, ∏ q ∈ s.erase a,
      PowerSeries.C (R := K) (w q/(w q-w a)) * (1-PowerSeries.C (R := K) (w q)⁻¹*PowerSeries.X)) := by
      rw [hpart, mul_one]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      rw [← mul_prod_erase _ _ ha, mul_assoc, ← prod_mul_distrib]
      congr 1
      apply prod_congr rfl
      intro q hq
      rw [← hclear _ (mem_of_mem_erase hq)]
      ring

/-- Resum all nonempty occupied subsets of a finite family. The empty subset
contributes exactly one to the original product. -/
theorem finite_pole_product_resummed {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (w : ι → K) (hinj : Set.InjOn w s)
    (hz : ∀ q ∈ s, w q ≠ 0) (g b : ι → K⟦X⟧)
    (hclear : ∀ q ∈ s, g q * (1-PowerSeries.C (R := K) (w q)⁻¹*PowerSeries.X) = b q) :
    (∏ q ∈ s, (1+g q)) - 1 =
      ∑ a ∈ s, g a * ∏ q ∈ s.erase a, (1+PowerSeries.C (R := K) (w q/(w q-w a))*b q) := by
  let c (a q : ι) := PowerSeries.C (R := K) (w q/(w q-w a))*b q
  let f (t : Finset ι) (a : ι) := g a * ∏ q ∈ t.erase a, c a q
  let occ (a : ι) := ((s.erase a).powerset).image (insert a)
  have hm (t : Finset ι) (a : ι) : t ∈ s.powerset ∧ a ∈ t ↔ t ∈ occ a ∧ a ∈ s := by
    constructor
    · rintro ⟨ht,ha⟩
      have hts := mem_powerset.mp ht
      exact ⟨mem_image.mpr ⟨t.erase a, mem_powerset.mpr (erase_subset_erase a hts),
        insert_erase ha⟩, hts ha⟩
    · rintro ⟨ht,ha⟩
      obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
      refine ⟨mem_powerset.mpr ?_, mem_insert_self _ _⟩
      exact insert_subset ha ((mem_powerset.mp hu).trans (erase_subset _ _))
  have hz0 : (∅ : Finset ι) ∈ s.powerset := by simp
  have hs : (∏ q ∈ s, (1 + g q)) - 1 = ∑ t ∈ s.powerset, ∑ a ∈ t, f t a := by
    rw [prod_one_add]
    rw [← sum_erase_add _ (fun t : Finset ι => ∏ q ∈ t, g q) hz0]
    rw [← sum_erase_add _ (fun t : Finset ι => ∑ a ∈ t, f t a) hz0]
    simp only [prod_empty, sum_empty, add_sub_cancel_right, add_zero]
    apply sum_congr rfl
    intro t ht
    obtain ⟨hne,hts⟩ := mem_erase.mp ht
    have hsub := mem_powerset.mp hts
    exact finite_distinguished_pole_product t w (nonempty_iff_ne_empty.mpr hne)
      (hinj.mono hsub) (fun q hq => hz q (hsub hq)) g b (fun q hq => hclear q (hsub hq))
  rw [hs, sum_comm' hm]
  apply sum_congr rfl
  intro a _
  dsimp only [occ]
  rw [sum_image]
  · rw [prod_one_add, mul_sum]
    apply sum_congr rfl
    intro u hu
    have hnot : a ∉ u := fun ha => (mem_erase.mp ((mem_powerset.mp hu) ha)).1 rfl
    simp only [f, c, erase_insert hnot]
  · intro u hu v hv he
    have hnu : a ∉ u := fun ha => (mem_erase.mp ((mem_powerset.mp hu) ha)).1 rfl
    have hnv : a ∉ v := fun ha => (mem_erase.mp ((mem_powerset.mp hv) ha)).1 rfl
    simpa only [erase_insert hnu, erase_insert hnv] using congrArg (fun t : Finset ι => t.erase a) he

/-- The finite form of the normalized cycle-pole series, with D the abstract
cycle probability series and B its cleared nonconstant part. -/
theorem finite_cycle_series_poles {K ι : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (w : ι → K) (hinj : Set.InjOn w s) (hz : ∀ q ∈ s, w q ≠ 0)
    (D : K⟦X⟧) :
    (∏ q ∈ s, PowerSeries.rescale (w q)⁻¹ D) - 1 =
      ∑ a ∈ s, PowerSeries.rescale (w a)⁻¹ (D-1) *
        ∏ q ∈ s.erase a, (1+PowerSeries.C (R := K) (w q/(w q-w a))*
          PowerSeries.rescale (w q)⁻¹ ((D-1)*(1-PowerSeries.X))) := by
  let g := fun q => PowerSeries.rescale (w q)⁻¹ (D-1)
  let b := fun q => PowerSeries.rescale (w q)⁻¹ ((D-1)*(1-PowerSeries.X))
  have hc : ∀ q ∈ s, g q*(1-PowerSeries.C (R := K) (w q)⁻¹*PowerSeries.X) = b q := by
    intro q _
    simp only [g,b,map_mul,map_sub,map_one,PowerSeries.rescale_X]
  have h := finite_pole_product_resummed s w hinj hz g b hc
  simpa only [g,b,map_sub,map_one,add_comm (1:K⟦X⟧),sub_add_cancel] using h

/-- Degree j+1 of one primitive factor. Its pole power is j rather than j+1
because the partial-fraction multiplier contributes w_q. -/
theorem finite_cycle_primitive_coeff {K : Type*} [Field K] (wa wq : K)
    (hq : wq ≠ 0) (B : K⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (R := K) (j+1) (PowerSeries.C (R := K) (wq/(wq-wa)) * PowerSeries.rescale wq⁻¹ B) =
      ((wq⁻¹)^j/(wq-wa))*PowerSeries.coeff (R := K) (j+1) B := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_succ]
  by_cases he : wq-wa = 0
  · simp [he]
  · field_simp [hq, he] <;> ring

#print axioms finite_pole_partition
#print axioms finite_distinguished_pole_product
#print axioms finite_pole_product_resummed
#print axioms finite_cycle_series_poles
#print axioms finite_cycle_primitive_coeff
end OpenMathResearch.LongCycleExcedances
