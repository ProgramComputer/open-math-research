import PrimitiveCheckerMass
import SignedStarEnvelope

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real

def checkerShape (K i : ℕ) (U X : ℝ) : ℝ :=
  (checkerDegreeFloor i-1/(K:ℝ))*U/(192*X)

/-- A uniform linear certificate for the literal occupied primitives. The only
lattice hypotheses are finite head bounds and the rational scalar tail bound. -/
theorem literal_checker_scaled_linear_envelope {n k K N J cap G : ℕ}
    (hK : 193 ≤ K) (hKk : K ≤ k) (hn : 0 < n)
    {X θ U A₀ : ℝ} (hX : 0 < X) (hnX : (n:ℝ) ≤ X*k)
    (hS : 0 < sin θ) (hU : 0 < U) (hUs : U ≤ (n:ℝ)*sin θ^2)
    (hA₀ : 0 < A₀)
    (b : ℕ → ℝ)
    (hb : ∀ s, PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) = (b s:ℂ))
    (hatom : b k=1/(k:ℝ))
    (hfirst : ∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1)))
    (hjump : |b (2*k)| ≤ 1/(4*(k:ℝ)^2))
    (hblock : ∀ j s : ℕ, 2 ≤ j → j*k < s → s ≤ (j+1)*k →
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2))
    (l : ℕ → ℕ) (V T : ℕ → ℝ)
    (hguard : ∀ i, 4 ≤ i → i ≤ cap → 1 ≤ 3*checkerShape K i U X*(2*(J:ℝ)+1)^2)
    (hhead : ∀ i, 4 ≤ i → i ≤ cap → ∀ t ∈ signedCenters J,
      (∑ q ∈ (signedHead J).erase t, oddStarTerm (checkerShape K i U X) t q) ≤ V i)
    (htail : ∀ i, 4 ≤ i → i ≤ cap →
      oTail (checkerShape K i U X) (2*(J:ℝ)+1)/(190*checkerShape K i U X*(2*(J:ℝ)+1)) ≤ T i)
    (hnn : ∀ i, 4 ≤ i → i ≤ cap → 0 ≤ V i+T i/2)
    (hround : ∀ i, 4 ≤ i → i ≤ cap →
      checkerDegreeMass K i*(V i+T i/2)/A₀ ≤ (l i:ℝ)/G)
    (A : Finset ℤ) (a : ℤ) :
    ∀ i ≤ cap, (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤ A₀/((k:ℝ)*sin θ)*((l i:ℝ)/G) := by
  intro i hi
  by_cases h4 : 4 ≤ i
  · have hbound : 1/(K:ℝ) < checkerDegreeFloor i := by
      have hKinv : (1:ℝ)/(K:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num)
        (by exact_mod_cast (show 2 ≤ K by omega))
      have hg : (1:ℝ) ≤ checkerDegreeFloor i := by
        by_cases he : i=4
        · simp [checkerDegreeFloor,he]
        · simp only [checkerDegreeFloor,if_neg he]
          have ht : (4:ℝ) ≤ ((i-1:ℕ):ℝ) := by exact_mod_cast (show 4 ≤ i-1 by omega)
          linarith
      linarith
    have hc : 0 < checkerShape K i U X :=
      div_pos (mul_pos (sub_pos.mpr hbound) hU) (by positivity)
    have hstar := signed_star_envelope A a J hc (hguard i h4 hi) (hhead i h4 hi) (htail i h4 hi)
    have hmass := primitive_all_checker_bin_mass (N:=N) (i:=i) (by omega) hKk b hatom hfirst hjump hblock
    have hKS : 0 < (k:ℝ)*sin θ := mul_pos (Nat.cast_pos.mpr (by omega)) hS
    have hraw := literal_bin_linear_bound hK hKk hn hX hnX hbound.le
      (fun _ hs => checker_degree_floor_le (by omega) h4 hs) hS hU.le hUs hKS le_rfl
      (hnn i h4 hi) b hb hmass A a hstar
    apply hraw.trans
    calc
      _ = A₀/((k:ℝ)*sin θ)*(checkerDegreeMass K i*(V i+T i/2)/A₀) := by
        field_simp [hA₀.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hround i h4 hi) (by positivity)
  · have hzero : (binLinear (A.erase a)
        (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i = 0 := by
      rw [binLinear,Polynomial.finsetSum_coeff]
      apply sum_eq_zero
      intro q _
      simp only [literalMarkedPrimitive,coeff_forgetDegree_markDegreeBin,←sum_filter]
      change (∑ s ∈ primitiveDegrees k N i, _) = 0
      rw [primitiveDegrees_below_four (by omega : 0 < k) (by omega : i < 4),sum_empty]
    rw [hzero]
    positivity
theorem literal_checker_linear_envelope {n k K N J cap G : ℕ}
    (hK : 193 ≤ K) (hKk : K ≤ k) (hn : 0 < n)
    {X θ U A₀ : ℝ} (hX : 0 < X) (hnX : (n:ℝ) ≤ X*k)
    (hS : 0 < sin θ) (hU : 0 < U) (hUs : U ≤ (n:ℝ)*sin θ^2)
    (hA₀ : 0 < A₀) (hA : A₀ ≤ (k:ℝ)*sin θ)
    (b : ℕ → ℝ)
    (hb : ∀ s, PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) = (b s:ℂ))
    (hatom : b k=1/(k:ℝ))
    (hfirst : ∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1)))
    (hjump : |b (2*k)| ≤ 1/(4*(k:ℝ)^2))
    (hblock : ∀ j s : ℕ, 2 ≤ j → j*k < s → s ≤ (j+1)*k →
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2))
    (l : ℕ → ℕ) (V T : ℕ → ℝ)
    (hguard : ∀ i, 4 ≤ i → i ≤ cap → 1 ≤ 3*checkerShape K i U X*(2*(J:ℝ)+1)^2)
    (hhead : ∀ i, 4 ≤ i → i ≤ cap → ∀ t ∈ signedCenters J,
      (∑ q ∈ (signedHead J).erase t, oddStarTerm (checkerShape K i U X) t q) ≤ V i)
    (htail : ∀ i, 4 ≤ i → i ≤ cap →
      oTail (checkerShape K i U X) (2*(J:ℝ)+1)/(190*checkerShape K i U X*(2*(J:ℝ)+1)) ≤ T i)
    (hnn : ∀ i, 4 ≤ i → i ≤ cap → 0 ≤ V i+T i/2)
    (hround : ∀ i, 4 ≤ i → i ≤ cap →
      checkerDegreeMass K i*(V i+T i/2)/A₀ ≤ (l i:ℝ)/G)
    (A : Finset ℤ) (a : ℤ) :
    ∀ i ≤ cap, (binLinear (A.erase a)
      (fun q => forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) a q))).coeff i ≤ (l i:ℝ)/G := by
  intro i hi
  have hKS : 0 < (k:ℝ)*sin θ := mul_pos (Nat.cast_pos.mpr (by omega)) hS
  have h := literal_checker_scaled_linear_envelope hK hKk hn hX hnX hS hU hUs hA₀
    b hb hatom hfirst hjump hblock l V T hguard hhead htail hnn hround A a i hi
  exact h.trans (mul_le_of_le_one_left (by positivity) ((div_le_one hKS).mpr hA))

/-- Both finite checkers satisfy the stronger discrete tail guard on
every relevant bin of every aspect slab. -/
theorem checker_shape_tail_guard {K i J : ℕ} (hK : 208 ≤ K) (hi : 4 ≤ i)
    (hJ : 31 ≤ J) {X : ℝ} (hX : 0 < X) (hXm : X ≤ 48) :
    1 ≤ 3*checkerShape K i (6/5) X*(2*(J:ℝ)+1)^2 := by
  have hkR : (208:ℝ) ≤ K := by exact_mod_cast hK
  have hiR : (1:ℝ) ≤ checkerDegreeFloor i := by
    by_cases he : i=4
    · simp [checkerDegreeFloor,he]
    · simp only [checkerDegreeFloor,if_neg he]
      have ht : (4:ℝ) ≤ ((i-1:ℕ):ℝ) := by exact_mod_cast (show 4 ≤ i-1 by omega)
      linarith
  have hkInv : (1:ℝ)/(K:ℝ) ≤ 1/208 :=
    one_div_le_one_div_of_le (by norm_num) hkR
  have hm : ((1:ℝ)-1/208)*(6/5)/(192*48) ≤ checkerShape K i (6/5) X := by
    unfold checkerShape
    apply div_le_div₀ (mul_nonneg (by linarith only [hiR,hkInv]) (by norm_num)) _ (by positivity) (by linarith)
    linarith
  have hp : (63:ℝ) ≤ 2*(J:ℝ)+1 := by
    have h : (31:ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 3))
    (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 63) hp 2) (by norm_num)
    (mul_nonneg (by norm_num) ((by norm_num : (0:ℝ) ≤ (1-1/208)*(6/5)/(192*48)).trans hm))
  exact (by norm_num : (1:ℝ) ≤ 3*((1-1/208)*(6/5)/(192*48))*63^2).trans hh

#print axioms checker_shape_tail_guard
#print axioms literal_checker_linear_envelope
end OpenMathResearch.LongCycleExcedances
