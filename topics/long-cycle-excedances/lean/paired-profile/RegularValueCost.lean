import RegularNumeratorBin
import NonprincipalValueCost
import LinearSlabs

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real CycleProbability

def scaledRegularTerm (k n t : ℕ) (d : ℕ→ℝ) (θ : ℝ) (a : ℤ) : ℝ :=
  if k < n+1-t then
    (k:ℝ)/sin θ*|numeratorDiff k d (n+1-t)| *
      ‖(pairedPoleDenom (cos θ) (sin θ) a)⁻¹‖^(n+1-t)*|sin ((n:ℝ)*θ)| else 0

def regularPoleBudget (lower upper b : ℕ) (A₀ : ℝ) (a : ℤ) : ℝ :=
  if b+5 ≤ 5*upper then regularBinWeight lower b/A₀*valueKernel lower upper b a else 0

theorem regularBinWeight_nonneg (lower b : ℕ) : 0 ≤ regularBinWeight lower b := by
  dsimp only [regularBinWeight]
  split <;> positivity

theorem regularPoleBudget_nonneg (lower upper b : ℕ) {A₀ : ℝ} (hA : 0 < A₀) (a : ℤ) :
    0 ≤ regularPoleBudget lower upper b A₀ a := by
  unfold regularPoleBudget
  split
  · exact mul_nonneg (div_nonneg (regularBinWeight_nonneg ..) hA.le)
      (inv_nonneg.mpr (Even.pow_nonneg (by decide : Even 96) _))
  · rfl

theorem regular_term_on_bin {k n lower upper b t : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hk : 192 ≤ k) (hl : 0 < lower) (hX : n ≤ upper*k) (hlo : lower*k ≤ n)
    (ht₁ : 4*t ≤ k*b) (ht₂ : k*b ≤ 5*t) {θ A₀ : ℝ} (hS : 0 < sin θ)
    (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (hA : 0 < A₀) (hAS : A₀ ≤ (k:ℝ)*sin θ) (a : ℤ) :
    scaledRegularTerm k n t d θ a ≤ regularPoleBudget lower upper b A₀ a := by
  by_cases hr : k < n+1-t
  · have hk0 : 0 < k := by omega
    have hkr : 0 < (k:ℝ) := by exact_mod_cast hk0
    have hr' : k ≤ n-t := by omega
    have he := value_bin_active hk0 hX ht₂ hr'
    rw [scaledRegularTerm,if_pos hr,regularPoleBudget,if_pos he]
    have hκ := regular_numerator_strict_bin hd (by omega) hlo ht₁ hr
    have hbase : (k:ℝ)/sin θ*|numeratorDiff k d (n+1-t)| ≤ regularBinWeight lower b/A₀ := by
      calc
        _ = (k^2*|numeratorDiff k d (n+1-t)|)/((k:ℝ)*sin θ) := by field_simp <;> ring
        _ ≤ regularBinWeight lower b/A₀ :=
          div_le_div₀ (regularBinWeight_nonneg ..) hκ hA hAS
    have hker := value_kernel_on_bin hk hl hX hlo ht₁ hr' hS hU a
    have habs : |sin ((n:ℝ)*θ)| ≤ 1 := abs_le.mpr ⟨neg_one_le_sin _,sin_le_one _⟩
    apply (mul_le_of_le_one_right (by positivity) habs).trans
    exact mul_le_mul hbase hker (by positivity) (div_nonneg (regularBinWeight_nonneg ..) hA.le)
  · rw [scaledRegularTerm,if_neg hr]
    exact regularPoleBudget_nonneg _ _ _ hA _

theorem regular_one_pole (slab : Fin 9) {k n lower : ℕ} {d : ℕ→ℝ} (hd : Spec k d)
    (hn : 10000 ≤ n) (hnX : n ≤ linearSlabX slab*k) (hl : 0 < lower) (hlo : lower*k ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hU : 6/5 ≤ (n:ℝ)*sin θ^2) (A : Finset ℤ) (a : ℤ) (q : ℕ→ℕ)
    (hq : q 0=linearScale) (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m,
      (ij.1+1)*linearSlabTable slab (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*linearScale) :
    (∑ t ∈ range (n+2), scaledRegularTerm k n t d θ a*
      ‖PowerSeries.coeff (R := ℂ) t (∏ v ∈ A.erase a, (1+occupiedPrimitive k (cos θ) (sin θ) a v))‖) ≤
        ∑ b ∈ range 241, regularPoleBudget lower (linearSlabX slab) b (linearSlabLower slab) a*
          ((q b:ℝ)/linearScale) := by
  have h48 : linearSlabX slab ≤ 48 := by fin_cases slab <;> norm_num [linearSlabX]
  have hk : 192 ≤ k := by
    have hmax := hnX.trans (Nat.mul_le_mul_right k h48)
    omega
  have hA : 0 < (linearSlabLower slab:ℝ) := by fin_cases slab <;> norm_num [linearSlabLower,linearSlabQuarter]
  have hAS := (linearSlabInputs slab hn hnX hS hU).2
  apply finite_weighted_bin_cost A a (by omega : 0 < k) (cos θ) (sin θ) _ _ _ _ _ _ _
    (by decide : 0 < linearScale) (linearSlabTable slab) q (by simp [linearSlabTable,literalLinearTable]) hq
    (fun i _ => literal_slab_linear_envelope_of_spec slab hn hnX hS hU hd A a i) hrec
  · intro v _ t ht
    exact occupied_primitive_below hd (by omega) ht _ _ a v
  · intro t
    unfold scaledRegularTerm
    split <;> positivity
  · exact fun b => regularPoleBudget_nonneg _ _ _ hA _
  · intro b hb
    simp only [regularPoleBudget,if_neg (show ¬b+5 ≤ 5*linearSlabX slab by omega)]
  · intro b t _ ht₁ ht₂
    exact regular_term_on_bin hd hk hl hnX hlo ht₁ ht₂ hS hU hA hAS a

#print axioms regular_term_on_bin
#print axioms regular_one_pole
end OpenMathResearch.LongCycleExcedances
