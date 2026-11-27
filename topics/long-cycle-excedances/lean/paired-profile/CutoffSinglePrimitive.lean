import PrimitiveNumeratorInputs
import SignedStarEnvelope
import RepositoryRegularCost

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

/-- The cutoff atom's one-primitive coefficient is evaluated at one degree.
The scale bound depends only on the lower aspect endpoint. -/
theorem cutoff_single_weight {n k lower : ℕ} {d : ℕ → ℝ} (hd : Spec k d)
    (hk : 2 ≤ k) (hl : 4 ≤ lower) (hnl : lower*k ≤ n) :
    (k:ℝ)^2*|numeratorDiff k d (n+1-k)| ≤ 1/(2*((lower-1).factorial:ℝ)) := by
  let j := (n-k)/k
  have hkL : k ≤ lower*k := by
    simpa using Nat.mul_le_mul_right k (by omega : 1 ≤ lower)
  have hnk : k ≤ n := hkL.trans hnl
  have hk0 : 0 < k := by omega
  have hlk : (lower-1)*k+k = lower*k := by
    rw [← Nat.succ_mul, show (lower-1).succ = lower by omega]
  have hjl : lower-1 ≤ j := (Nat.le_div_iff_mul_le hk0).2 (by omega)
  have hjlo : j*k < n+1-k := by
    have hb : j*k ≤ n-k := Nat.div_mul_le_self (n-k) k
    omega
  have hjhi : n+1-k ≤ (j+1)*k := by
    have hb := (Nat.div_lt_iff_lt_mul hk0).1 (show (n-k)/k < j+1 by omega)
    omega
  have h := hd.numeratorDiff_factorial_block hk0 (by omega : 2 ≤ j) hjlo hjhi
  have hkr : (0:ℝ) < k := by exact_mod_cast hk0
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg (k:ℝ))).trans
  calc
    _ = 1/(2*(j.factorial:ℝ)) := by
      field_simp [hkr.ne', show (j.factorial:ℝ) ≠ 0 by positivity] <;> ring
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by
      have hf : ((lower-1).factorial:ℝ) ≤ j.factorial := by
        exact_mod_cast Nat.factorial_le hjl
      linarith)

private theorem cutoff_single_gap (C : ℝ) {S : ℝ} (hS : 0 ≤ S) (q a : ℤ) :
    ‖pairedPoleDenom C S q-pairedPoleDenom C S a‖ =
      |primitiveOddNumber q-primitiveOddNumber a| * S := by
  rw [pairedPoleDenom_sub,norm_mul,norm_mul,Complex.norm_I,one_mul,norm_mul,
    show ‖(2:ℂ)‖ = 2 by norm_num,← Int.cast_sub,Complex.norm_intCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hS]
  have h : primitiveOddNumber q-primitiveOddNumber a = 2*((q:ℝ)-(a:ℝ)) := by
    unfold primitiveOddNumber
    ring
  rw [h,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), Int.cast_sub]

/-- The term selecting exactly one primitive in the cutoff numerator. The
triangle bound retains its genuine degree and all off-diagonal divisors. -/
def singleCutoffPrimitiveCost (k n : ℕ) (d : ℕ → ℝ) (θ : ℝ) (A : Finset ℤ) : ℝ :=
  ∑ a ∈ A, ((k:ℝ)/sin θ*|numeratorDiff k d k| *
    ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k*|sin ((n:ℝ)*θ)|) *
    (∑ q ∈ A.erase a,
      ‖PowerSeries.coeff (R := ℂ) (n+1-k) (occupiedPrimitive k (cos θ) (sin θ) a q)‖)

/-- Split the two poles at their own degree fractions. The outer pole sees
the cutoff degree k, and the inner pole sees the fixed remaining degree. -/
theorem single_cutoff_primitive_lattice {n k K lower : ℕ} {d : ℕ → ℝ} (hd : Spec k d)
    (hK : 193 ≤ K) (hKk : K ≤ k) (hl : 4 ≤ lower) (hnl : lower*k ≤ n)
    {X U θ A₀ M V : ℝ} (hX : 0 < X) (hnX : (n:ℝ) ≤ X*k) (hU : 0 ≤ U)
    (hS : 0 < sin θ) (hUs : U ≤ (n:ℝ)*sin θ^2)
    (hA₀ : 0 < A₀) (hA : A₀ ≤ (k:ℝ)*sin θ) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (A : Finset ℤ)
    (hmass : (∑ a ∈ A, oddBinKernel (U/(192*X)) a) ≤ M)
    (hstar : ∀ a,
      (∑ q ∈ A.erase a, oddStarTerm ((((lower-1:ℕ):ℝ)-1/K)*U/(192*X)) a q) ≤ V) :
    singleCutoffPrimitiveCost k n d θ A ≤ M*V / (2*((lower-1).factorial:ℝ)*A₀^2) := by
  let T := n+1-k
  let g : ℝ := ((lower-1:ℕ):ℝ)
  let c := (g-1/K)*U/(192*X)
  let c₀ := U/(192*X)
  have hk : 0 < k := by omega
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hn : 0 < n := by
    have hkl : k ≤ lower*k := by
      simpa using Nat.mul_le_mul_right k (by omega : 1 ≤ lower)
    omega
  have hs : k ≤ T := by
    have := Nat.mul_le_mul_right k (show 2 ≤ lower by omega)
    dsimp only [T]
    omega
  have hg : 1/(K:ℝ) ≤ g := by
    have hk' : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have ht : (1:ℝ) ≤ g := by
      dsimp only [g]
      exact_mod_cast (show 1 ≤ lower-1 by omega)
    exact ((div_le_one (by positivity)).2 hk').trans ht
  have hgT : g ≤ (T:ℝ)/k := by
    apply (le_div_iff₀ hkr).2
    have hk' : (lower-1)*k+k = lower*k := by
      rw [←Nat.succ_mul,show (lower-1).succ = lower by omega]
    have hm : (lower-1)*k ≤ T := by dsimp only [T]; omega
    dsimp only [g]
    exact_mod_cast hm
  obtain ⟨hb,ha,_,_,_⟩ := primitive_checker_numerator_inputs hd (by omega : 2 ≤ k)
  have hpoint (a q : ℤ) :
      ‖PowerSeries.coeff (R := ℂ) T (occupiedPrimitive k (cos θ) (sin θ) a q)‖ ≤
        |numeratorDiff k d T|/sin θ*oddStarTerm c a q := by
    have hr := primitive_bin_kernel hK hKk hn hs hX hnX hg hgT hS hU hUs q
    rw [literalPrimitive_norm_formula hk hs _ hS.ne',hb,norm_mul,norm_div,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,cutoff_single_gap _ hS.le]
    change ‖(pairedPoleDenom (cos θ) (sin θ) q)⁻¹‖^(T-1)/
        (|primitiveOddNumber q-primitiveOddNumber a| * sin θ)*|numeratorDiff k d T| ≤ _
    apply (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hr (mul_nonneg (abs_nonneg _) hS.le)) (abs_nonneg _)).trans_eq
    dsimp only [oddStarTerm]
    ring
  have hinner (a : ℤ) :
      (∑ q ∈ A.erase a, ‖PowerSeries.coeff (R := ℂ) T
        (occupiedPrimitive k (cos θ) (sin θ) a q)‖) ≤
      |numeratorDiff k d T|/sin θ*V := by
    apply (sum_le_sum (fun q _ => hpoint a q)).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (hstar a) (div_nonneg (abs_nonneg _) hS.le)
  have houter (a : ℤ) :
      (k:ℝ)/sin θ*|numeratorDiff k d k| *‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k*|sin ((n:ℝ)*θ)| ≤
        (sin θ)⁻¹*oddBinKernel c₀ a := by
    have hyk : 1/X ≤ (k:ℝ)/n :=
      (div_le_div_iff₀ hX (Nat.cast_pos.mpr hn)).2 (by simpa [mul_comm] using hnX)
    have h := primitive_angular_bernoulli_kernel (r := k) hn (by omega : 192 ≤ k) a hS
      (by positivity : 0 ≤ 1/X) hyk hU hUs
    have hker : ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^k ≤ oddBinKernel c₀ a := by
      have he : 1/X*U/192 = U/(192*X) := by ring
      simpa only [oddBinKernel,c₀,he] using h
    have hbn : |numeratorDiff k d k| = 1/(k:ℝ) := by
      rw [hd.numeratorDiff_at_cutoff hk, abs_of_nonneg (by positivity)]
    have he : (k:ℝ)/sin θ*(1/(k:ℝ)) = (sin θ)⁻¹ := by
      field_simp [hkr.ne',hS.ne'] <;> ring
    rw [hbn,he]
    apply (mul_le_of_le_one_right (by positivity) (abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩)).trans
    exact mul_le_mul_of_nonneg_left hker (by positivity)
  let B := 1/(2*((lower-1).factorial:ℝ))
  have hs₂ : 0 < sin θ^2 := sq_pos_of_pos hS
  have hcoeff : |numeratorDiff k d T|/sin θ^2 ≤ B/A₀^2 := by
    have h := cutoff_single_weight hd (by omega : 2 ≤ k) hl hnl
    have he : |numeratorDiff k d T|/sin θ^2 =
        ((k:ℝ)^2*|numeratorDiff k d T|)/(((k:ℝ)*sin θ)^2) := by
      field_simp [hkr.ne',hS.ne'] <;> ring
    rw [he]
    exact div_le_div₀ (by positivity) h (by positivity)
      (pow_le_pow_left₀ hA₀.le hA 2)
  calc
    _ ≤ ∑ a ∈ A, ((sin θ)⁻¹*oddBinKernel c₀ a)*
        (|numeratorDiff k d T|/sin θ*V) := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul (houter a) (hinner a) (sum_nonneg (fun _ _ => norm_nonneg _))
        (mul_nonneg (by positivity) (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _)))
    _ = (|numeratorDiff k d T|/sin θ^2*V)*(∑ a ∈ A, oddBinKernel c₀ a) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      simp only [div_eq_mul_inv, inv_pow, pow_two]
      ring
    _ ≤ (B/A₀^2*V)*M := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcoeff hV) hmass
        (sum_nonneg (fun _ _ => inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))) (by positivity)
    _ = _ := by dsimp only [B]; ring

#print axioms cutoff_single_weight
#print axioms single_cutoff_primitive_lattice
end OpenMathResearch.LongCycleExcedances
