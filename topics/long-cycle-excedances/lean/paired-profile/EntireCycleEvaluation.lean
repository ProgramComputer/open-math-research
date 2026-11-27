import CutoffCycleSeriesRecurrence
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
noncomputable section

namespace OpenMathResearch.LongCycleExcedances
open Finset
open scoped PowerSeries

/-- Absolute evaluation of a complex formal power series at the specified point. -/
def CoeffHasSum (F : ℂ⟦X⟧) (v s : ℂ) : Prop :=
  HasSum (fun n => PowerSeries.coeff (R := ℂ) n F * v^n) s

theorem CoeffHasSum.one (v : ℂ) : CoeffHasSum 1 v 1 := by
  unfold CoeffHasSum
  apply (hasSum_ite_eq (0:ℕ) (1:ℂ)).congr_fun
  intro n
  by_cases h : n=0 <;> simp [PowerSeries.coeff_one,h,eq_comm]

private theorem eval_X (v : ℂ) : CoeffHasSum PowerSeries.X v v := by
  unfold CoeffHasSum
  convert (hasSum_ite_eq (1:ℕ) v) using 1
  funext n
  by_cases h : n=1 <;> simp [PowerSeries.coeff_X,h,eq_comm]

private theorem eval_sub {F G : ℂ⟦X⟧} {v s t : ℂ}
    (hf : CoeffHasSum F v s) (hg : CoeffHasSum G v t) : CoeffHasSum (F-G) v (s-t) := by
  simpa only [CoeffHasSum,map_sub,sub_mul] using hf.sub hg

theorem CoeffHasSum.mul_series {F G : ℂ⟦X⟧} {v s t : ℂ}
    (hf : CoeffHasSum F v s) (hg : CoeffHasSum G v t) : CoeffHasSum (F*G) v (s*t) := by
  let f (n : ℕ) := PowerSeries.coeff (R := ℂ) n F*v^n
  let g (n : ℕ) := PowerSeries.coeff (R := ℂ) n G*v^n
  have h1 : HasSum f s := hf
  have h2 : HasSum g t := hg
  have hab := summable_mul_of_summable_norm h1.summable.norm h2.summable.norm
  have hconv := h1.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal h2.summable hab
  rw [h1.tsum_eq,h2.tsum_eq] at hconv
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm
    h1.summable.norm h2.summable.norm).of_norm.hasSum
  rw [←hconv] at hs
  refine hs.congr_fun (fun n => ?_)
  rw [PowerSeries.coeff_mul,Finset.sum_mul]
  apply sum_congr rfl
  intro p hp
  dsimp only [f,g]
  have he : p.1 + p.2 = n := by simpa using hp
  rw [← he,pow_add]
  ring

private def atom (m : ℕ) (c : ℂ) : ℂ⟦X⟧ := PowerSeries.C (R := ℂ) c * PowerSeries.X^m

private theorem coeff_atom_pow (m j n : ℕ) (c : ℂ) :
    PowerSeries.coeff (R := ℂ) n ((atom m c)^j) = if n=m*j then c^j else 0 := by
  rw [atom,mul_pow,←map_pow,←pow_mul,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]
  split <;> simp_all

private theorem atom_vanishes {m : ℕ} (hm : 0 < m) (c : ℂ) : VanishesBelow 1 (atom m c) := by
  intro n hn
  have h := coeff_atom_pow m 1 n c
  simpa [show n≠m by omega] using h

private theorem eval_exp_atom {m : ℕ} (hm : 0 < m) (c v : ℂ) :
    CoeffHasSum (cutoffExp (atom m c)) v (Complex.exp (c*v^m)) := by
  let f (n : ℕ) := PowerSeries.coeff (R := ℂ) n (cutoffExp (atom m c))*v^n
  have hi : Function.Injective (fun j : ℕ => m*j) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_left hm h
  have hz (n : ℕ) (hn : n ∉ Set.range (fun j : ℕ => m*j)) : f n = 0 := by
    have hne (j : ℕ) : n ≠ m*j := fun e => hn ⟨j,e.symm⟩
    simp [f,coeff_cutoffExp (k:=1) (by decide) (atom_vanishes hm c),coeff_atom_pow,hne]
  apply (hi.hasSum_iff hz).mp
  rw [Complex.exp_eq_exp_ℂ]
  apply (NormedSpace.expSeries_div_hasSum_exp (c*v^m)).congr_fun
  intro j
  change f (m*j)=(c*v^m)^j/(j.factorial:ℂ)
  simp only [f,coeff_cutoffExp (k:=1) (by decide) (atom_vanishes hm c),Nat.div_one]
  rw [sum_eq_single j]
  · simp only [coeff_atom_pow,ite_true,eq_self,mul_pow,←pow_mul]
    ring
  · intro b _ hbj
    rw [coeff_atom_pow,if_neg (fun h => hbj (hi h.symm)),zero_div]
  · intro h
    exfalso
    apply h
    exact mem_range.mpr (by have := Nat.le_mul_of_pos_left j hm; omega)


private theorem cutoff_cleared_one :
    cutoffCycleSeries 1 * (1 - PowerSeries.X) = 1 := by
  have spec : CycleProbability.Spec 1 (fun _ => 1) := by
    constructor
    · rfl
    · intro r hr h; omega
    · intro r hr
      simp [show r-1+1=r by omega]
  have hc (n : ℕ) : PowerSeries.coeff (R := ℂ) n (cutoffCycleSeries 1) = 1 := by
    simpa using coeff_cutoffCycleSeries_eq_of_spec spec (by decide) n
  ext n
  have hX := PowerSeries.coeff_mul_X_pow' (cutoffCycleSeries 1) 1 n
  simp only [pow_one] at hX
  rw [mul_sub,mul_one,map_sub,hX,hc,PowerSeries.coeff_one]
  cases n <;> simp [hc]

private theorem cutoff_step (m : ℕ) :
    cutoffCycleSeries (m+2) = cutoffCycleSeries (m+1) *
      cutoffExp (atom (m+1) (-(1/((m:ℂ)+1)))) := by
  have hl : cutoffLog (m+2) = cutoffLog (m+1) + atom (m+1) (-(1/((m:ℂ)+1))) := by
    ext n
    simp only [cutoffLog,map_add,PowerSeries.coeff_mk,atom,PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow]
    by_cases hn : n = m + 1
    · subst n
      simp [show ¬ (m + 2 ≤ m + 1) by omega]
    · by_cases h : m + 2 ≤ n
      · simp [h,show m + 1 ≤ n by omega,hn]
      · simp [h,show ¬ (m + 1 ≤ n) by omega,hn]
  unfold cutoffCycleSeries
  rw [hl]
  apply cutoffExp_add (k:=1) (by decide) _ (atom_vanishes (by omega) _)
  intro n hn
  exact vanishesBelow_cutoffLog (m+1) n (by omega)

/-- The denominator-cleared probability series evaluates absolutely at every complex point. -/
theorem cleared_cutoff_hasSum (m : ℕ) (v : ℂ) :
    CoeffHasSum (cutoffCycleSeries (m+1) * (1-PowerSeries.X)) v
      (Complex.exp (-(∑ i ∈ range m, v^(i+1)/((i:ℂ)+1)))) := by
  induction m with
  | zero => simpa [cutoff_cleared_one] using CoeffHasSum.one v
  | succ m ih =>
    rw [cutoff_step]
    rw [show cutoffCycleSeries (m+1) * cutoffExp (atom (m+1) (-(1/((m:ℂ)+1)))) *
          (1-PowerSeries.X) = (cutoffCycleSeries (m+1) * (1-PowerSeries.X)) *
          cutoffExp (atom (m+1) (-(1/((m:ℂ)+1)))) by ring]
    rw [sum_range_succ,neg_add,Complex.exp_add]
    convert CoeffHasSum.mul_series ih (eval_exp_atom (m:=m+1) (by omega) (-(1/((m:ℂ)+1))) v) using 2 <;> first | ring | (congr 1 <;> ring)

theorem cutoff_numerator_hasSum (m : ℕ) (v : ℂ) :
    CoeffHasSum (cutoffCycleNumerator (m+1)) v
      (Complex.exp (-(∑ i ∈ range m, v^(i+1)/((i:ℂ)+1))) - (1-v)) := by
  have h := eval_sub (cleared_cutoff_hasSum m v) (eval_sub (CoeffHasSum.one v) (eval_X v))
  simpa only [cutoffCycleNumerator,sub_mul,one_mul] using h

#print axioms cutoff_numerator_hasSum

end OpenMathResearch.LongCycleExcedances
