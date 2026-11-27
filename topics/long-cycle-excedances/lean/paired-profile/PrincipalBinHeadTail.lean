import CenteredMarkedProduct
import LiteralPrincipalTilt

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Polynomial Real CycleProbability

private theorem bin_head_bound {ι : Type*} (A : Finset ι) (p : ι→ℝ[X])
    (hp : ∀ q ∈ A, ∀ b, 0 ≤ (p q).coeff b) (hz : ∀ q ∈ A, (p q).coeff 0=0)
    {G J : ℕ} (hG : 0 < G) (l q : ℕ→ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ i ≤ J, (binLinear A p).coeff i ≤ (l i:ℝ)/G)
    (hrec : ∀ m < J, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G) :
    ∀ b ≤ J, (binFull A p).coeff b ≤ (q b:ℝ)/G := by
  intro b hb
  by_cases h : b=0
  · subst b
    rw [binFull,←constantCoeff_apply,map_prod]
    rw [prod_eq_one (fun i hi => by simp [constantCoeff_apply,hz i hi]),hq,div_self (by exact_mod_cast hG.ne')]
  · exact (bin_integer_multiple_bound A p hp hz hG l q hl hq hL hrec (by omega : 0 < b) hb).1

/-- The two marked-product arguments use the same ceiling-rounded product bound. -/
theorem literal_rounded_head_bound (A : Finset ℤ) (a : ℤ) {k N G J : ℕ} (hk : 0 < k) (C S : ℝ)
    (hG : 0 < G) (l q : ℕ→ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ i ≤ J, (binLinear (A.erase a) (fun v => forgetDegree (literalMarkedPrimitive k N C S a v))).coeff i
      ≤ (l i:ℝ)/G)
    (hrec : ∀ m < J, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G) :
    ∀ b ≤ J, (binFull (A.erase a) (fun v => forgetDegree (literalMarkedPrimitive k N C S a v))).coeff b
      ≤ (q b:ℝ)/G := by
  apply bin_head_bound _ _ _ _ hG l q hl hq hL hrec
  · intro v _ b
    rw [literalMarkedPrimitive,coeff_forgetDegree_markDegreeBin]
    exact sum_nonneg (fun _ _ => by split <;> positivity)
  · intro v _
    rw [literalMarkedPrimitive,coeff_forgetDegree_markDegreeBin]
    apply sum_eq_zero
    intro t ht
    have hs := (mem_Icc.mp ht).1
    have hh := (degreeBin_bounds hk hs).1
    apply if_neg
    intro he
    rw [he,Nat.mul_zero] at hh
    omega

theorem forget_marked_absolute_product (T : Finset ℤ) (k N : ℕ) (C S : ℝ) (a : ℤ) :
    forgetDegree (markedAbsoluteProduct T k N (occupiedPrimitive k C S a)) =
      binFull T (fun v => forgetDegree (literalMarkedPrimitive k N C S a v)) := by
  change (mapRingHom (evalRingHom 1)) (∏ v ∈ T, (1+literalMarkedPrimitive k N C S a v)) = _
  simp only [map_prod,map_add,map_one]
  rfl

/-- The complete scaled principal convolution is controlled by the first
241 finite bin budgets and a fixed analytic tail, uniformly in the finite pole set. -/
theorem principal_bin_head_tail {j n lower G : ℕ} {d : ℕ→ℝ} (hd : Spec (j+2) d)
    (hn : 10000 ≤ n) (hkn : n ≤ 48*(j+2)) (hlo : lower*(j+2) ≤ n)
    {θ : ℝ} (hS : 0 < sin θ) (hangle : 6/5 ≤ (n:ℝ)*sin θ^2)
    (A : Finset ℤ) (hG : 0 < G) (l q : ℕ→ℕ) (hl : l 0=0) (hq : q 0=G)
    (hL : ∀ N i, i ≤ 240 →
      (binLinear (A.erase 0) (fun v => forgetDegree (literalMarkedPrimitive (j+2) N (cos θ) (sin θ) 0 v))).coeff i
        ≤ (l i:ℝ)/G)
    (hrec : ∀ m < 240, ∑ ij ∈ antidiagonal m, (ij.1+1)*l (ij.1+1)*q ij.2 ≤ (m+1)*q (m+1)*G) :
    let w := pairedPoleDenom (cos θ) (sin θ) 0
    let Q := ∏ v ∈ A.erase 0, (1+occupiedPrimitive (j+2) (cos θ) (sin θ) 0 v)
    let value := Complex.exp (∑ v ∈ A.erase 0, principalLogIntegral j (w/pairedPoleDenom (cos θ) (sin θ) v))
    let c := Real.exp (-cycleHarmonic (j+1))
    2*‖((j+2:ℕ):ℂ)*((∑ t ∈ range (n+1), (cutoffWeight (j+2) d (n-t):ℂ)*
       (PowerSeries.coeff (R := ℂ) t Q*w^t))-(c:ℂ)*value)‖ <
      2*(∑ b ∈ range 241, centeredErrorBound (centeredBinIndex lower b)*((q b:ℝ)/G))+1/10000 := by
  let T := A.erase 0
  let k := j+2
  let F := occupiedPrimitive k (cos θ) (sin θ) 0
  let E (b:ℕ) := centeredErrorBound (centeredBinIndex lower b)
  let head := ∑ b ∈ range 241, E b*((q b:ℝ)/G)
  let tail : ℝ := (4/7)/(9/8:ℝ)^240*exp 14
  have hF (v : ℤ) (_ : v ∈ T) (t : ℕ) (ht : t < k) : PowerSeries.coeff (R := ℂ) t (F v)=0 :=
    occupied_primitive_below hd (by omega) ht _ _ 0 v
  have hQ := occupied_product_hasSum_integral j (cos θ) hS.ne' 0 T (by simp [T])
    (fun v _ => principal_pole_ratio_norm_le _ hS.ne' v)
  have hw := principal_angular_unit θ
  have hcost (N : ℕ) : markedCost (markedAbsoluteProduct T k N F) lower ≤ head+tail := by
    let P := markedAbsoluteProduct T k N F
    let p (v:ℤ) := forgetDegree (literalMarkedPrimitive k N (cos θ) (sin θ) 0 v)
    have heq : forgetDegree P = binFull T p := forget_marked_absolute_product ..
    have hh := literal_rounded_head_bound A 0 (by omega : 0 < j+2) (cos θ) (sin θ) hG l q hl hq (hL N) hrec
    have hp (b:ℕ) : 0 ≤ (forgetDegree P).coeff b := by
      rw [forgetDegree,coeff_map]
      have hgeom := marked_product_geometry T (k:=k) (by dsimp [k]; omega) N
        (fun v s => ‖PowerSeries.coeff (R := ℂ) s (F v)‖) (fun _ _ _ => norm_nonneg _)
      change 0 ≤ (P.coeff b).eval 1
      rw [eval_eq_sum_range]
      simp only [one_pow,mul_one]
      exact sum_nonneg (fun t _ => hgeom.1 b t)
    have h := cost_split_head_tail (forgetDegree P) P.natDegree 240 natDegree_map_le E (fun t => (q t:ℝ)/G)
      (H:=4/7) (base:=9/8) (by norm_num) (by norm_num) hp (fun _ => by positivity)
      (fun b => ⟨centeredErrorBound_nonneg _,centeredErrorBound_le _⟩) (heq ▸ hh)
    have ht : (4/7:ℝ)/(9/8:ℝ)^240*(forgetDegree P).eval (9/8) ≤ tail :=
      mul_le_mul_of_nonneg_left (heq.symm ▸ literal_principal_tilt hd hn hkn hS hangle A N)
        (by positivity : 0 ≤ (4/7:ℝ)/(9/8:ℝ)^240)
    exact h.trans (add_le_add (le_refl head) ht)
  have h := centered_marked_cost (m:=j+1) (n:=n) T F hd (by omega) hlo hF hw hQ hcost
  dsimp only
  have hscale : (((j+1:ℕ):ℝ)+1:ℂ)=((j+2:ℕ):ℂ) := by push_cast; ring
  rw [hscale] at h
  have ht : 2*tail < 1/10000 := by
    dsimp only [tail]
    linarith only [symmetric_bin_tail_reserve]
  change 2*_ < 2*head+1/10000
  linarith only [h,ht]

#print axioms literal_rounded_head_bound
#print axioms principal_bin_head_tail
end OpenMathResearch.LongCycleExcedances
