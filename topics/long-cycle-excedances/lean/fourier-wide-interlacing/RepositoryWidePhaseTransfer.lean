import RepositoryMiddleCells
import LiteralDiscretePoleMoments

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open OpenMathResearch.LongCycleExcedances LongCycles Set Real

/-- The exact pointwise centered-row conclusion used by the common-circle root
transfer. Separate contour estimates can supply it over their cutoff ranges. -/
def WideCenteredRows (n k : ℕ) : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    let p := coherentPole s 0
    let r := ‖p‖
    let S := π/r
    let C := s/r
    let T := seriesValue (coherentTilt k (-exp (-s)))
    let U := ‖T p‖
    let a := T p/(U:ℂ)*((r:ℂ)/p)^(n+1)
    let Y := fun q : ℕ => r^(q+1)/(2*U) *
      ((enumerator q k).eval (-Real.exp (-s))/((1+Real.exp (-s))^(q+1)*q.factorial))
    1 ≤ (n:ℝ)*S^2 →
    |Y n-a.re| < 37/300 ∧ |Y (n+1)-C*Y n-S*a.im| < 29/100*S ∧
      ((enumerator n k).eval (-Real.exp (-s))=0 →
        99/100 < |a.im| ∧ 0<(enumerator (n+1) k).eval (-Real.exp (-s))*a.im)

/-- The old row crosses a full middle phase interval, and the original next
row has the alternating sign at every old zero in that interval. -/
theorem original_wide_phase_cell_of_centered {n k j : ℕ} (hk : 7 ≤ k) (hkn : k ≤ n)
    (hcentered : WideCenteredRows n k)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hm : b^2+π^2 ≤ (n:ℝ)*π^2)
    (hφa : principalPhaseX n k a=((j+1:ℕ):ℝ)*π) (hφb : principalPhaseX n k b=(j:ℝ)*π) :
    (∃ x ∈ Ioo a b, (enumerator n k).eval (-exp (-x))=0) ∧
    (∀ x ∈ Ioo a b, (enumerator n k).eval (-exp (-x))=0 →
      0 < (-1:ℝ)^(j+1)*(enumerator (n+1) k).eval (-exp (-x))) := by
  let P (q : ℕ) (x : ℝ) := (enumerator q k).eval (-exp (-x))
  let A (x : ℝ) := ‖coherentPole x 0‖^(n+1)/(2*highAngleAmplitude k x)/((1+exp (-x))^(n+1)*n.factorial)
  have hA (x : ℝ) : 0<A x := by
    have hr := coherentPole_near_pos x
    have hu := highAngleAmplitude_pos (by omega : 2≤k) x
    dsimp only [A]; positivity
  have hbounds (x : ℝ) (hxin : x ∈ Icc a b) :
      |A x*P n x-cos (principalPhaseX n k x)| ≤ 1/2 ∧
      (P n x=0 → 0<P (n+1) x * (-sin (principalPhaseX n k x))) := by
    have hs := ha.trans hxin.1
    have hr := coherentPole_near_pos x
    have he : ‖coherentPole x 0‖^2=x^2+π^2 := by
      change ‖numeratorPole x 0‖^2 = x^2+π^2
      simpa only [Int.cast_zero,mul_zero,zero_add,one_mul] using literal_pole_norm_sq x 0
    have hmid : 1 ≤ (n:ℝ)*(π/‖coherentPole x 0‖)^2 := by
      rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos hr),one_mul,he]
      linarith only [hm,pow_le_pow_left₀ hs hxin.2 2]
    let T := seriesValue (coherentTilt k (-exp (-x)))
    let p := coherentPole x 0
    let u := T p/(‖T p‖:ℂ)*((‖p‖:ℂ)/p)^(n+1)
    obtain ⟨hu,_,hz⟩ := hcentered x hs hmid
    have huEq : u=highAnglePrincipal n k x/(highAngleAmplitude k x:ℂ) := by
      unfold highAnglePrincipal highAngleUnit highAngleAmplitude
      dsimp only [u,p,T]; ring
    obtain ⟨hcos,hsin⟩ := original_middle_phase_readout (n:=n) (by omega : 2≤k) x
    change (highAnglePrincipal n k x/(highAngleAmplitude k x:ℂ)).re=_ at hcos
    rw [←huEq] at hcos hsin
    have hid : A x*P n x=‖p‖^(n+1)/(2*‖T p‖)*(P n x/((1+exp (-x))^(n+1)*n.factorial)) := by
      dsimp only [A,p,T,highAngleAmplitude]; ring
    constructor
    · rw [hid,←hcos]; exact hu.le.trans (by norm_num)
    · intro h0
      rw [←hsin]
      exact (hz h0).2
  exact signed_true_phase_cell_anti hab j (P n) (P (n+1)) A (principalPhaseX n k)
    ((enumerator n k).continuous.comp (continuous_exp.comp continuous_neg).neg).continuousOn
    ((original_middle_phase_strictAnti hk hkn b hm).mono
      (fun _ h => ⟨ha.trans h.1,h.2⟩)) hφa hφb (fun x _ => hA x)
    (fun x h => (hbounds x h).1) (fun x h => (hbounds x ⟨h.1.le,h.2.le⟩).2)

#print axioms original_wide_phase_cell_of_centered
end RepositoryQuotientAudit
