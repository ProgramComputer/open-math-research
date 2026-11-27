import LiteralLinearTable
import PrimitiveNumeratorInputs
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
namespace OpenMathResearch.LongCycleExcedances
open Finset Real
open scoped PowerSeries

def linearSlabX (j : Fin 9) : ℕ := ![6,10,16,22,28,34,40,44,48] j
def linearSlabQuarter (j : Fin 9) : ℕ := ![73,43,27,19,15,12,10,9,9] j
def linearSlabK (j : Fin 9) : ℕ := 10000/linearSlabX j
def linearSlabLower (j : Fin 9) : ℚ := (linearSlabQuarter j:ℚ)/4
def linearSlabTable (j : Fin 9) : ℕ → ℕ :=
  literalLinearTable (linearSlabK j) (linearSlabX j) (linearSlabLower j)

private theorem linearSlabConstants (j : Fin 9) :
    0 < linearSlabX j ∧ linearSlabX j ≤ 48 ∧ 208 ≤ linearSlabK j ∧
    0 < (linearSlabLower j:ℝ) ∧
    ((linearSlabLower j:ℝ)*(linearSlabX j:ℝ))^2 ≤ 12000 := by
  fin_cases j <;> norm_num [linearSlabX,linearSlabQuarter,linearSlabK,linearSlabLower]

theorem linearSlabInputs (j : Fin 9) {n k : ℕ} (hn : 10000 ≤ n)
    (hnX : n ≤ linearSlabX j*k) {θ : ℝ} (hS : 0 < sin θ)
    (hUs : (6/5:ℝ) ≤ (n:ℝ)*sin θ^2) :
    linearSlabK j ≤ k ∧ (linearSlabLower j:ℝ) ≤ (k:ℝ)*sin θ := by
  obtain ⟨hX,_,_,hA,hconst⟩ := linearSlabConstants j
  have hXR : (0:ℝ)<linearSlabX j := by exact_mod_cast hX
  have hnorm : (n:ℝ) ≤ (linearSlabX j:ℝ)*(k:ℝ) := by exact_mod_cast hnX
  have hnr : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hK : linearSlabK j ≤ k := by
    unfold linearSlabK
    apply Nat.lt_succ_iff.mp
    exact (Nat.div_lt_iff_lt_mul hX).mpr (by
      have hc : 10000 ≤ linearSlabX j*k := hn.trans hnX
      rw [Nat.mul_comm (linearSlabX j) k] at hc
      rw [Nat.succ_mul]
      omega)
  have hsq : (n:ℝ)^2*sin θ^2 ≤ ((linearSlabX j:ℝ)*(k:ℝ)*sin θ)^2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnorm 2) (sq_nonneg _)
  have hl : (12000:ℝ) ≤ (n:ℝ)^2*sin θ^2 := by
    have h := mul_le_mul_of_nonneg_left hUs (Nat.cast_nonneg n)
    nlinarith only [h,hnr]
  have ht := (sq_le_sq₀ (by positivity : 0 ≤ (linearSlabLower j:ℝ)*(linearSlabX j:ℝ))
      (by positivity : 0 ≤ (linearSlabX j:ℝ)*(k:ℝ)*sin θ)).mp (hconst.trans (hl.trans hsq))
  refine ⟨hK,le_of_mul_le_mul_right ?_ hXR⟩
  convert ht using 1 <;> ring

theorem literal_slab_scaled_linear_envelope_of_spec (j : Fin 9) {n k N : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX j*k)
    {θ : ℝ} (hS : 0 < sin θ) (hUs : (6/5:ℝ) ≤ (n:ℝ)*sin θ^2)
    {d : ℕ → ℝ} (hd : CycleProbability.Spec k d)
    (A : Finset ℤ) (a : ℤ) (i : ℕ) :
    (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤
      ((linearSlabLower j:ℝ)/((k:ℝ)*sin θ))*((linearSlabTable j i:ℝ)/linearScale) := by
  obtain ⟨hX,hX48,hK208,hA, _⟩ := linearSlabConstants j
  have hKk := (linearSlabInputs j hn hnX hS hUs).1
  have hk : 2 ≤ k := by omega
  obtain ⟨hb,ha,hfirst,hjump,hblock⟩ := primitive_checker_numerator_inputs hd hk
  let c := fun v => linearShape (linearSlabK j) v (linearSlabX j)
  let V := fun v => (linearHead (c v):ℝ)/linearScale
  let T := fun v => 2*(linearHalfTail (c v):ℝ)/linearScale
  have shape (v : ℕ) := cast_linearShape (linearSlabK j) v (linearSlabX j)
  refine literal_checker_scaled_linear_envelope (J:=31) (cap:=i) (G:=linearScale)
    (X:=(linearSlabX j:ℝ)) (by omega) hKk (by omega)
    (by exact_mod_cast hX) (by exact_mod_cast hnX) hS (by norm_num) hUs hA _
    hb ha hfirst hjump hblock (linearSlabTable j) V T ?_ ?_ ?_ ?_ ?_ A a i le_rfl
  · intro v hv _
    exact checker_shape_tail_guard hK208 hv (by decide) (by exact_mod_cast hX) (by exact_mod_cast hX48)
  · intro v _ _ t ht
    rw [← shape v]
    exact linearHead_upper _ t ht
  · intro v hv _
    rw [← shape v]
    rw [show 2*((31:ℕ):ℝ)+1=63 by norm_num]
    exact linearTail_upper (c v)
  · intro _ _ _
    dsimp only [V,T]
    have hG : (0:ℝ) ≤ linearScale := Nat.cast_nonneg _
    exact add_nonneg (div_nonneg (Nat.cast_nonneg _) hG)
      (div_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hG) (by norm_num))
  · intro v hv _
    exact linearTable_rounding (linearSlabK j) (linearSlabX j) (linearSlabLower j) v hv hA.ne'
theorem literal_slab_linear_envelope_of_spec (j : Fin 9) {n k N : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX j*k)
    {θ : ℝ} (hS : 0 < sin θ) (hUs : (6/5:ℝ) ≤ (n:ℝ)*sin θ^2)
    {d : ℕ → ℝ} (hd : CycleProbability.Spec k d)
    (A : Finset ℤ) (a : ℤ) (i : ℕ) :
    (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤
      (linearSlabTable j i:ℝ)/linearScale := by
  have hAS := (linearSlabInputs j hn hnX hS hUs).2
  have hA := (linearSlabConstants j).2.2.2.1
  have hKS : 0 < (k:ℝ)*sin θ := hA.trans_le hAS
  exact (literal_slab_scaled_linear_envelope_of_spec (N:=N) j hn hnX hS hUs hd A a i).trans
    (mul_le_of_le_one_left (by positivity) ((div_le_one hKS).mpr hAS))

/-- The linear input to the literal rounded-product theorem, instantiated
for every actual slab. No finite numerical head, tail, or rounding input remains. -/
theorem original_slab_linear_envelope (j : Fin 9) {n k N : ℕ}
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX j*k)
    {θ : ℝ} (hS : 0 < sin θ) (hUs : (6/5:ℝ) ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (a : ℤ) (i : ℕ) :
    (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤
      (linearSlabTable j i:ℝ)/linearScale := by
  have hK := (linearSlabConstants j).2.2.1
  have hKk := (linearSlabInputs j hn hnX hS hUs).1
  have hk : 2 ≤ k := by omega
  exact literal_slab_linear_envelope_of_spec j hn hnX hS hUs
    (CycleProbability.originalProbability_spec hk) A a i

#print axioms literal_slab_scaled_linear_envelope_of_spec
#print axioms original_slab_linear_envelope
#print axioms linearSlabInputs
#print axioms literal_slab_linear_envelope_of_spec
end OpenMathResearch.LongCycleExcedances
