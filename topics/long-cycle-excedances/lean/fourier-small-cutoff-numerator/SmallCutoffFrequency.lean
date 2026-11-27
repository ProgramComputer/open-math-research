import SmallCutoffPoisson
import HighHeightContraction

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset Real Filter Topology

theorem radial_frequency_sum_at (k : ℕ) (s R D u v : ℝ) (hs : 0 < s) (hsR : s ≤ R)
    (hk : 0 < k) (hD : 0 ≤ D) (hR : R-s ≤ D*(s/k))
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 < v-D/k)
    (hprefix : ∀ x : ℝ, 0 ≤ x → u*k ≤ x →
      (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((1-v)*x)) (F : Finset ℕ) :
    (∑ a ∈ F, radialFrequency k s R a) ≤
      (u*k/s)*exp (D*u) + 1/((v-D/k)*s) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hR0 : 0 ≤ R := hs.le.trans hsR
  have hcut : (0:ℝ) ≤ u*k/s := by positivity
  apply positive_mesh_split hcut (exp_pos _).le (by norm_num : (0:ℝ)≤1) (mul_pos hc hs) F
  · intro a _ ha
    let A := ((a+1:ℕ):ℝ)
    have hA : 0 ≤ A := by positivity
    have hAs : A*s ≤ u*k := (le_div_iff₀ hs).mp ha
    unfold radialFrequency
    calc
      _ ≤ exp (-A*s)*exp (A*R) :=
        mul_le_mul_of_nonneg_left (sum_le_exp_of_nonneg (mul_nonneg hA hR0) _) (exp_pos _).le
      _ = exp (A*(R-s)) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := by
        apply exp_le_exp.mpr
        apply (mul_le_mul_of_nonneg_left hR hA).trans
        have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hkR).mpr hAs) hD
        convert h using 1
        ring
  · intro a _ ha
    let A := ((a+1:ℕ):ℝ)
    have hA : 0 ≤ A := by positivity
    have hAs : u*k < A*s := (div_lt_iff₀ hs).mp ha
    have hAr : u*k ≤ A*R :=
      hAs.le.trans (mul_le_mul_of_nonneg_left hsR hA)
    unfold radialFrequency
    rw [one_mul]
    calc
      _ ≤ exp (-A*s)*exp ((1-v)*(A*R)) :=
        mul_le_mul_of_nonneg_left (hprefix _ (mul_nonneg hA hR0) hAr) (exp_pos _).le
      _ ≤ _ := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hR hA
        have h' := mul_le_mul_of_nonneg_left hsR (show 0 ≤ v*A by positivity)
        change -A*s+(1-v)*(A*R) ≤ -A*((v-D/k)*s)
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h,h']

theorem tail_frequency_sum_at (k : ℕ) (s t b : ℝ) (hk : 0 < k) (ht : 0 < t) (hb : 0 < b)
    (hgap : b*s/k ≤ s-t) (hts : t < s)
    (F : Finset ℕ) (J : ℕ → Finset ℕ) (hJ : ∀ a j, j ∈ J a → k ≤ j) :
    (∑ a ∈ F, tailFrequency s t J a) ≤ ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + 2/b := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have ht0 : 0 < t := ht
  have hs0 : 0 < s := ht0.trans hts
  have hc : 0 < s-t := by linarith
  have hsplit :
      (∑ a ∈ F, tailFrequency s t J a) ≤
        ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + (2*t/k)/(s-t) := by
    refine positive_mesh_split (by positivity) (exp_pos _).le (by positivity) hc F _ ?_ ?_
    · intro a _ ha
      let A := ((a+1:ℕ):ℝ)
      have hA : 0 < A := by positivity
      have hA1 : 1 ≤ A := by
        change (1:ℝ) ≤ ((a+1:ℕ):ℝ)
        exact_mod_cast (by omega : 1 ≤ a+1)
      have ha' : A*(2*t) ≤ k := (le_div_iff₀ (by positivity : 0<2*t)).mp ha
      unfold tailFrequency
      calc
        _ ≤ exp (-A*s)/A * exp (2*(A*t)-(2/3:ℝ)*k) :=
          mul_le_mul_of_nonneg_left (poisson_upper_tilt (by positivity) _ _ (hJ a)) (by positivity)
        _ = exp (-A*s+(2*(A*t)-(2/3:ℝ)*k))/A := by
          rw [exp_add]
          ring
        _ ≤ exp (-A*s+(2*(A*t)-(2/3:ℝ)*k)) := by
          apply div_le_self (exp_pos _).le hA1
        _ ≤ _ := by
          apply exp_le_exp.mpr
          nlinarith only [ha', mul_le_mul_of_nonneg_left hts.le hA.le]
    · intro a _ ha
      let A := ((a+1:ℕ):ℝ)
      have hA : 0 < A := by positivity
      have ha' : (k:ℝ) < A*(2*t) := (div_lt_iff₀ (by positivity : 0<2*t)).mp ha
      have hi : (1:ℝ)/A ≤ 2*t/k := by
        apply (div_le_div_iff₀ hA hk0).mpr
        nlinarith only [ha']
      unfold tailFrequency
      calc
        _ ≤ exp (-A*s)/A * exp (A*t) :=
          mul_le_mul_of_nonneg_left (expTerms_le (by positivity) _) (by positivity)
        _ = (1/A)*exp (-A*(s-t)) := by
          rw [show -A*(s-t)=-A*s+A*t by ring, exp_add]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hi (exp_pos _).le
  apply hsplit.trans
  apply add_le_add_left
  have h : b*s ≤ (s-t)*(k:ℝ) := (div_le_iff₀ hk0).mp hgap
  have hbt : b*t ≤ (s-t)*(k:ℝ) :=
    (mul_le_mul_of_nonneg_left hts.le hb.le).trans h
  apply (div_le_div_iff₀ hc hb).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk0).mpr
  nlinarith only [hbt]

theorem radial_tsum_bound_at (k : ℕ) (s R D u v : ℝ) (hs : 0 < s) (hsR : s ≤ R)
    (hk : 0 < k) (hD : 0 ≤ D) (hR : R-s ≤ D*(s/k)) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 < v-D/k)
    (hprefix : ∀ x : ℝ, 0 ≤ x → u*k ≤ x →
      (∑ i ∈ range (k-1), x^i/(i.factorial:ℝ)) ≤ exp ((1-v)*x)) :
    Summable (radialFrequency k s R) ∧
      (∑' a, radialFrequency k s R a) ≤
        (u*k/s)*exp (D*u) + 1/((v-D/k)*s) := by
  have hn (a : ℕ) : 0 ≤ radialFrequency k s R a := by
    unfold radialFrequency
    have hR0 : 0 ≤ R := hs.le.trans hsR
    positivity
  have H := radial_frequency_sum_at k s R D u v hs hsR hk hD hR hu hv hc hprefix
  exact ⟨summable_of_sum_le hn H, (summable_of_sum_le hn H).tsum_le_of_sum_le H⟩

theorem high_height_tail_tsum_at (k : ℕ) (s t b : ℝ) (hk : 0 < k) (ht : 0 < t) (hb : 0 < b)
    (hgap : b*s/k ≤ s-t) (hts : t < s) :
    Summable (highHeightTail k s t) ∧
      (∑' a, highHeightTail k s t a) ≤ ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + 2/b := by
  have hd (a : ℕ) :
      Summable (fun j : ℕ => (((a+1:ℕ):ℝ)*t)^(j+k)/((j+k).factorial:ℝ)) := by
    exact (NormedSpace.expSeries_div_hasSum_exp ℝ (((a+1:ℕ):ℝ)*t)).summable.comp_injective
      (add_left_injective k)
  have hn (a : ℕ) : 0 ≤ highHeightTail k s t a := by
    unfold highHeightTail
    have ht0 : 0 ≤ t := by linarith
    exact mul_nonneg (by positivity) (tsum_nonneg (by intro; positivity))
  have HB (F : Finset ℕ) : (∑ a ∈ F, highHeightTail k s t a) ≤ ((k:ℝ)/(2*t))*exp (-(k:ℝ)/6) + 2/b := by
    let block (N : ℕ) : Finset ℕ := (range N).map ⟨(·+k), add_left_injective k⟩
    have hBlock (N j : ℕ) (hj : j ∈ block N) : k ≤ j := by
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      simp
    have hterm (a : ℕ) : Tendsto (fun N : ℕ => tailFrequency s t (fun _ => block N) a)
        atTop (𝓝 (highHeightTail k s t a)) := by
      have h := (hd a).hasSum.mul_left (exp (-((a+1:ℕ):ℝ)*s)/((a+1:ℕ):ℝ))
      have h' := h.tendsto_sum_nat
      simpa only [highHeightTail, tailFrequency, block, sum_map, Function.Embedding.coeFn_mk, mul_sum] using h'
    exact le_of_tendsto_of_tendsto (tendsto_finset_sum F fun a _ => hterm a) tendsto_const_nhds
      (Eventually.of_forall fun N => tail_frequency_sum_at k s t b hk ht hb hgap hts F
        (fun _ => block N) (fun _ j hj => hBlock N j hj))
  exact ⟨summable_of_sum_le hn HB, (summable_of_sum_le hn HB).tsum_le_of_sum_le HB⟩

#print axioms radial_tsum_bound_at
#print axioms high_height_tail_tsum_at
end OpenMathResearch.LongCycleExcedances
