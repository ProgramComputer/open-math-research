import PrimitiveBinAssembly
import CutoffCycleSeriesRecurrence

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open CycleProbability Finset Real

theorem primitive_checker_numerator_inputs {k : ℕ} {d : ℕ → ℝ}
    (h : Spec k d) (hk : 2 ≤ k) :
    let b := numeratorDiff k d
    (∀ s, PowerSeries.coeff (R := ℂ) s ((cutoffCycleSeries k-1)*(1-PowerSeries.X)) = (b s:ℂ)) ∧
    b k=1/(k:ℝ) ∧
    (∀ s : ℕ, k < s → s < 2*k → b s = -1/((s:ℝ)*((s:ℝ)-1))) ∧
    |b (2*k)| ≤ 1/(4*(k:ℝ)^2) ∧
    (∀ j s : ℕ, 2 ≤ j → j*k < s → s ≤ (j+1)*k →
      |b s| ≤ 1/(2*(j.factorial:ℝ)*(k:ℝ)^2)) := by
  dsimp only
  have hj := h.numeratorDiff_at_twice_pos_lt hk
  exact ⟨fun _ => coeff_cutoffCycleNumerator_eq_of_spec h (by omega),
    h.numeratorDiff_at_cutoff (by omega), fun _ => h.numeratorDiff_between,
    (abs_of_pos hj.1).trans_le hj.2.le,
    fun _ _ => h.numeratorDiff_factorial_block (by omega)⟩

theorem original_checker_linear_envelope {n k K N J cap G : ℕ}
    (hK : 193 ≤ K) (hKk : K ≤ k) (hn : 0 < n)
    {X θ U A₀ : ℝ} (hX : 0 < X) (hnX : (n:ℝ) ≤ X*k)
    (hS : 0 < sin θ) (hU : 0 < U) (hUs : U ≤ (n:ℝ)*sin θ^2)
    (hA₀ : 0 < A₀) (hA : A₀ ≤ (k:ℝ)*sin θ)
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
  have hk : 2 ≤ k := by omega
  obtain ⟨hb,ha,hfirst,hjump,hblock⟩ :=
    primitive_checker_numerator_inputs (originalProbability_spec hk) hk
  exact literal_checker_linear_envelope hK hKk hn hX hnX hS hU hUs hA₀ hA _
    hb ha hfirst hjump hblock l V T hguard hhead htail hnn hround A a

#print axioms original_checker_linear_envelope

#print axioms primitive_checker_numerator_inputs
end OpenMathResearch.LongCycleExcedances
