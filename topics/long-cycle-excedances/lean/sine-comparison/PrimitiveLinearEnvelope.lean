import PrimitiveBinMass
import PrimitivePoleKernel

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def oddBinKernel (c : ℝ) (q : ℤ) : ℝ :=
  ((1+c*(primitiveOddNumber q^2-1))^96)⁻¹

theorem primitive_bin_kernel {n k K s : ℕ} (hK : 193 ≤ K) (hKk : K ≤ k)
    (hn : 0 < n) (hks : k ≤ s) {X g θ U : ℝ} (hX : 0 < X)
    (hnX : (n:ℝ) ≤ X*(k:ℝ)) (hg : 1/(K:ℝ) ≤ g)
    (hs : g ≤ (s:ℝ)/k) (hS : 0 < sin θ) (hU : 0 ≤ U)
    (hUs : U ≤ (n:ℝ)*sin θ^2) (q : ℤ) :
    ‖primitiveAngularPole q θ‖^(s-1) ≤ oddBinKernel ((g-1/(K:ℝ))*U/(192*X)) q := by
  have hk : (0:ℝ)<k := Nat.cast_pos.mpr (by omega)
  have hK' : (K:ℝ) ≤ k := by exact_mod_cast hKk
  have hK0 : (0:ℝ)<K := Nat.cast_pos.mpr (by omega)
  have hs1 : (1:ℕ) ≤ s := by omega
  have hy : 0 ≤ (g-1/(K:ℝ))/X := div_nonneg (sub_nonneg.mpr hg) hX.le
  have hc : (g-1/(K:ℝ))*k ≤ ((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub hs1,Nat.cast_one]
    have hs' := (le_div_iff₀ hk).mp hs
    have ht : (1/(K:ℝ))*k ≥ 1 := by
      rw [one_div_mul_eq_div]
      exact (one_le_div hK0).mpr hK'
    linarith only [hs',ht]
  have hny : ((g-1/(K:ℝ))/X)*(n:ℝ) ≤ (s-1:ℕ) := by
    apply (mul_le_mul_of_nonneg_left hnX hy).trans
    have he : ((g-1/(K:ℝ))/X)*(X*(k:ℝ)) = (g-1/(K:ℝ))*k := by
      field_simp [hX.ne'] <;> ring
    rw [he]
    exact hc
  have hyr : (g-1/(K:ℝ))/X ≤ ((s-1:ℕ):ℝ)/n :=
    (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr hny
  have h := primitive_angular_bernoulli_kernel hn (by omega : 192 ≤ s-1) q hS hy hyr hU hUs
  have he : (g-1/(K:ℝ))/X*U/192 = (g-1/(K:ℝ))*U/(192*X) := by ring
  simpa only [oddBinKernel,he] using h

private theorem odd_gap_denom_norm (C : ℝ) {S : ℝ} (hS : 0 ≤ S) (q a : ℤ) :
    ‖pairedPoleDenom C S q-pairedPoleDenom C S a‖ =
      |primitiveOddNumber q-primitiveOddNumber a| *S := by
  rw [pairedPoleDenom_sub,norm_mul,norm_mul,Complex.norm_I,one_mul,norm_mul,
    show ‖(2:ℂ)‖ = 2 by norm_num,← Int.cast_sub,Complex.norm_intCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hS]
  have h : primitiveOddNumber q-primitiveOddNumber a = 2*((q:ℝ)-(a:ℝ)) := by
    unfold primitiveOddNumber
    ring
  rw [h,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2), Int.cast_sub]

theorem literal_bin_linear_bound {n k K N i : ℕ} (hK : 193 ≤ K) (hKk : K ≤ k)
    (hn : 0 < n) {X g θ U V A₀ M : ℝ} (hX : 0 < X)
    (hnX : (n:ℝ) ≤ X*k) (hg : 1/(K:ℝ) ≤ g)
    (hdegree : ∀ s ∈ primitiveDegrees k N i, g ≤ (s:ℝ)/k)
    (hS : 0 < sin θ) (hU : 0 ≤ U) (hUs : U ≤ (n:ℝ)*sin θ^2)
    (hA₀ : 0 < A₀) (hA : A₀ ≤ (k:ℝ)*sin θ) (hV : 0 ≤ V)
    (b : ℕ → ℝ)
    (hb : ∀ s, PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) = (b s:ℂ))
    (hM : (k:ℝ)*(∑ s ∈ primitiveDegrees k N i, |b s|) ≤ M)
    (A : Finset ℤ) (a : ℤ)
    (hstar : (∑ q ∈ A.erase a, oddBinKernel ((g-1/(K:ℝ))*U/(192*X)) q /
      |primitiveOddNumber q-primitiveOddNumber a|) ≤ V) :
    (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤ M*V/A₀ := by
  let T := primitiveDegrees k N i
  let c := (g-1/(K:ℝ))*U/(192*X)
  let W := fun q => oddBinKernel c q/|primitiveOddNumber q-primitiveOddNumber a|
  have hpoint (q : ℤ) (hq : q ∈ A.erase a) (s : ℕ) (hs : s ∈ T) :
      ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k (cos θ) (sin θ) a q)‖ ≤
        |b s|/sin θ*W q := by
    have hks := (mem_Icc.mp (mem_filter.mp hs).1).1
    have hr := primitive_bin_kernel hK hKk hn hks hX hnX hg (hdegree s hs) hS hU hUs q
    have hk0 : 0 < k := by omega
    rw [literalPrimitive_norm_formula hk0 hks _ hS.ne',hb,norm_mul,norm_div,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,odd_gap_denom_norm _ hS.le]
    change ‖primitiveAngularPole q θ‖^(s-1) /
        (|primitiveOddNumber q-primitiveOddNumber a| *sin θ)*|b s| ≤ _
    apply (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hr (mul_nonneg (abs_nonneg _) hS.le)) (abs_nonneg _)).trans_eq
    dsimp [W,c]
    ring
  have hW : 0 ≤ ∑ q ∈ A.erase a, W q := by
    apply sum_nonneg
    intro q _
    dsimp [W,oddBinKernel]
    exact div_nonneg (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _)) (abs_nonneg _)
  have hB : 0 ≤ ∑ s ∈ T, |b s| := sum_nonneg (fun j _ => abs_nonneg _)
  have hk0 : (0:ℝ)<k := Nat.cast_pos.mpr (by omega)
  have heq : (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i =
      ∑ q ∈ A.erase a, ∑ s ∈ T, ‖PowerSeries.coeff (R := ℂ) s (occupiedPrimitive k (cos θ) (sin θ) a q)‖ := by
    rw [binLinear,Polynomial.finsetSum_coeff]
    apply sum_congr rfl
    intro q _
    simp only [literalMarkedPrimitive,coeff_forgetDegree_markDegreeBin,T,primitiveDegrees,sum_filter]
  calc
    _ = _ := heq
    _ ≤ ∑ q ∈ A.erase a, ∑ s ∈ T, |b s|/sin θ*W q :=
      sum_le_sum (fun q hq => sum_le_sum (fun s hs => hpoint q hq s hs))
    _ = ((k:ℝ)*(∑ s ∈ T, |b s|))*(∑ q ∈ A.erase a,W q)/((k:ℝ)*sin θ) := by
      simp only [div_eq_mul_inv,← sum_mul,← mul_sum]
      field_simp [hk0.ne',hS.ne'] <;> ring
    _ ≤ M*V/((k:ℝ)*sin θ) := div_le_div_of_nonneg_right (mul_le_mul hM hstar hW
      ((mul_nonneg hk0.le hB).trans hM)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg ((mul_nonneg hk0.le hB).trans hM) hV) hA₀ hA

#print axioms primitive_bin_kernel
#print axioms literal_bin_linear_bound
end OpenMathResearch.LongCycleExcedances
