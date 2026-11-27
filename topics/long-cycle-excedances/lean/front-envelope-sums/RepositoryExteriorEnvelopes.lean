import FrontLagSum
import FrontSmallCap
import FrontModulusJoin
import RepositoryExteriorCertificates
import RepositoryPolynomialFront

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Real Polynomial OpenMathResearch.LongCycleExcedances

/-- Ratio of the actual central coefficients for the exterior rank h. -/
def originalExteriorScale (n k h : ℕ) : ℝ :=
  (enumerator n k).coeff h / (enumerator n k).coeff (h+1)

/-- The per-index estimates on the literal exterior coefficient arrays imply
both interlacing conclusions for the large-size pair. -/
theorem original_interlacing_of_exterior_weighted_envelopes {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 7 ≤ k) (hkn : k ≤ n)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    let P := enumerator n k
    let V := originalFrontLag n k
    let H := uniformJoinRank n
    let J := ⌊sqrt (n:ℝ)/2⌋₊
    let h (i : Fin H) := i.val+1
    let a (i : Fin H) := P.coeff (h i)
    let u (i : Fin H) := originalExteriorScale n k (h i)
    let w (i : Fin H) := frontCoefficientWeight (h i) (7/8*u i) (9/8*u i)
    (∀ i, 0 < a i ∧ 0 < P.coeff (h i+1)) →
    (∀ i j, i < j → (9/8:ℝ)*u i ≤ (7/8:ℝ)*u j) →
    (∀ i, u i ≤ (51/5:ℝ)*((H:ℝ)/((H:ℝ)+1))^n) →
    (∀ i j, j < h i → |P.coeff j| * w i j ≤
      (51/10*a i)*(((h i-j:ℕ):ℝ)+1)*(1/300)^(h i-j)) →
    (∀ i j, h i+1 < j → |P.coeff j| * w i j ≤
      (9*a i)*(((j-(h i+1):ℕ):ℝ)+1)*(1/300)^(j-(h i+1))) →
    (∀ j ≤ J, |V.coeff j| ≤ (8/25)*|P.coeff j|) →
    (∀ i j, J < j → |V.coeff j| * w i j ≤
      (36*a i)*((j-(h i+1):ℕ):ℝ)*(((j-(h i+1):ℕ):ℝ)+1)*(1/300)^(j-(h i+1))) →
    StrictNegativeInterlacing P.divX (enumerator (n+1) k).divX (n-2) ∧
    WeakRealInterlacing P (enumerator (n+1) k) := by
  intro P V H J h a u w hpos horder hcap hleft hright hnear hfar
  let Q := enumerator (n+1) k
  let G (i : Fin H) := C (n:ℝ)*X+(1-X)*C (((h i):ℝ)+1)
  have hh (i : Fin H) : h i ≤ H := by
    dsimp [h]
    exact i.isLt
  have hu (i : Fin H) : 0 < u i := div_pos (hpos i).1 (hpos i).2
  have hc (i : Fin H) : P.coeff (h i+1) = a i/u i := by
    change P.coeff (h i+1) = a i/(a i/P.coeff (h i+1))
    field_simp [(hpos i).1.ne', (hpos i).2.ne']
  have hrec : Q = C (n:ℝ)*X*P+(1-X)*(X*P.derivative)+V := by
    have hi := (LongCycleBounds.Insertion.enumerator_succ (by omega : 2 ≤ k) :
      FrontInsertion P Q V (n:ℝ))
    change Q = C (n:ℝ)*X*P+X*(1-X)*P.derivative+V at hi
    rw [hi]
    ring
  have hcap' (i : Fin H) : (9/8:ℝ)*u i ≤ (459/40:ℝ)*((H:ℝ)/((H:ℝ)+1))^n := by
    have hi := mul_le_mul_of_nonneg_left (hcap i) (by norm_num : (0:ℝ) ≤ 9/8)
    convert hi using 1 <;> ring
  have hsmall (i : Fin H) : (9/8:ℝ)*u i ≤ 1/2 := by
    obtain ⟨hp,hb⟩ : 0 < (H:ℝ) ∧ ((H:ℝ)+1)^2 ≤ (9/25:ℝ)^2*n :=
      exterior_floor_budget hn
    exact ((hcap' i).trans_lt (front_cap_lt_half hn hp hb)).le
  have hgap (i : Fin H) : h i+2 ≤ J := front_lag_cutoff_gap hn (hh i)
  have hnW (i : Fin H) (j : ℕ) (hj : j ≤ J) : |V.coeff j| * w i j ≤
      (8/25)*(|P.coeff j| * w i j) := by
    have hp : 0 ≤ w i j := by
      have hi := hu i
      dsimp only [w,frontCoefficientWeight]
      split <;> positivity
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hnear j hj) hp
  have cert (i : Fin H) := front_certificates_of_weighted_envelopes P Q V
    (hpos i).1 (hu i) (hsmall i) (hgap i) rfl (hc i) hrec (hleft i) (hright i)
    (hnW i) (hfar i)
  exact original_interlacing_of_exterior_coefficient_bounds hn hk hkn hsize a u G
    (fun i => (hpos i).1) hu horder hcap' (fun i => (cert i).1) (fun i => (cert i).2)

#print axioms original_interlacing_of_exterior_weighted_envelopes
end RepositoryQuotientAudit
