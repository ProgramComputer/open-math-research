import RepositoryOrbitBaseline
import CutoffAcceptanceBudget
import RepositoryColorCombinatorial

set_option autoImplicit false
noncomputable section

namespace OpenMathResearch.LongCycleExcedances.ColorAnchor

/-- Both normalizations count the same word and permutation pairs. -/
theorem accepted_probability_eq_realCount (n p k : ℕ) :
    (Nat.card (Accepted n p k):ℝ)/((p.factorial:ℝ)*(p:ℝ)^n) =
      realCount n p k/(p:ℝ)^n := by
  unfold realCount normalizedCount taggedCount
  push_cast
  exact (div_div _ _ _).symm

/-- With a single color, every word and permutation is accepted once n≥k. -/
theorem realCount_one_color {n k : ℕ} (hkn : k ≤ n) : realCount n 1 k = 1 := by
  have all (w : Fin n → Fin 1) (π : Equiv.Perm (Fin 1)) (c : Fin 1) :
      k ≤ load w π c := by
    let e : {x : Fin n // π.SameCycle c (w x)} ≃ Fin n :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, by
          simpa only [show w x = c from Subsingleton.elim _ _] using
            (Equiv.Perm.SameCycle.rfl : π.SameCycle c c)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold load
    simpa only [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] using hkn
  let e : Accepted n 1 k ≃ (Fin n → Fin 1) × Equiv.Perm (Fin 1) :=
    { toFun := Subtype.val
      invFun := fun w => ⟨w, all w.1 w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : Nat.card (Accepted n 1 k) = 1 := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  have eprob := accepted_probability_eq_realCount n 1 k
  rw [h] at eprob
  simpa using eprob.symm

end OpenMathResearch.LongCycleExcedances.ColorAnchor

namespace RepositoryQuotientAudit
open LongCycles Real OpenMathResearch.LongCycleExcedances
open OpenMathResearch.LongCycleExcedances.ColorAnchor

private theorem alpha_front_sample_size {n p : ℕ} (hn : 10000 ≤ n) (hpq : 4*p^2 ≤ n) :
    200*p ≤ n := by
  by_cases hp : 50 ≤ p
  · have hpp : (50:ℝ) ≤ p := by exact_mod_cast hp
    have hpq' : 4*(p:ℝ)^2 ≤ n := by exact_mod_cast hpq
    have h := mul_nonneg (show (0:ℝ) ≤ p by positivity) (sub_nonneg.mpr hpp)
    exact_mod_cast (show 200*(p:ℝ) ≤ n by nlinarith only [hpq', h])
  · omega

private theorem alpha_front_transform_loss {n p : ℕ} (hp : 0 < p) :
    (1-1/(p:ℝ))^n ≤ exp (-((n:ℝ)/p)) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hlo : 0 ≤ 1-1/(p:ℝ) := sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
  have hhi : 1-1/(p:ℝ) ≤ exp (-(1/(p:ℝ))) := by
    linarith only [add_one_le_exp (-(1/(p:ℝ)))]
  calc
    _ ≤ (exp (-(1/(p:ℝ))))^n := pow_le_pow_left₀ hlo hhi n
    _ = _ := by rw [←exp_nat_mul]; congr 1; ring

private theorem alpha_front_ceil_pos {x : ℝ} (hx : 0 < x) : 0 < ⌈x⌉₊ := by
  by_contra! h
  exact hx.not_le (Nat.ceil_eq_zero.mp (by omega))

/-- Exact endpoint for the single-color sample. -/
theorem original_front_alpha_one {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (enumerator n k).coeff 1 = 1 := by
  have he := original_color_acceptance_error (p := 1) hn (by decide) hk
  simp only [realCount_one_color hkn, Nat.cast_one, one_pow, div_one, sub_self,
    zero_pow hn.ne', mul_zero] at he
  linarith only [he.1, he.2]

/-- The lower old-row envelope in the uniform exterior sector. The chosen
natural cutoff is the rounded-up value 4kp/(3n). -/
theorem original_front_alpha_lower {n p k : ℕ} (hn : 10000 ≤ n) (hk : 2 ≤ k)
    (hsector : 4000*k < n) (hp : 0 < p) (hrank : 4*p^2 ≤ n) :
    let a : ℝ := (k:ℝ)*p/n
    99/(100*(1+(8/3:ℝ)*a)) ≤ (enumerator n k).coeff p/(p:ℝ)^n := by
  let a : ℝ := (k:ℝ)*p/n
  let f : ℝ := realCount n p k/(p:ℝ)^n
  let α : ℝ := (enumerator n k).coeff p/(p:ℝ)^n
  have hn0 : 0 < n := by omega
  have hkn : k ≤ n := by omega
  have hn' : (10000:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by positivity
  have hpp : (0:ℝ) < p := by positivity
  have hap : 0 < a := by dsimp [a]; positivity
  have hnorm : 0 < 100*(1+(8/3:ℝ)*a) := by positivity
  change 99/(100*(1+(8/3:ℝ)*a)) ≤ α
  by_cases hone : p=1
  · subst p
    have hα : α = 1 := by simp [α,original_front_alpha_one hn0 hk hkn]
    rw [hα]
    exact (div_le_one hnorm).mpr (by nlinarith only [hap])
  let b : ℕ := ⌈(4/3:ℝ)*a⌉₊
  let d : ℝ := 2*(b:ℝ)-1
  have hbc : (4/3:ℝ)*a ≤ (b:ℝ) := Nat.le_ceil _
  have hb : 0 < b := alpha_front_ceil_pos (by positivity : 0 < (4/3:ℝ)*a)
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hd : 0 < d := by dsimp [d]; linarith only [hb1]
  have hble : b ≤ p := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
    have hp1 : (1:ℕ) ≤ p := hp
    have hθ : (4/3:ℝ)*a < (p:ℝ)/3000 := by
      have hs : 4000*(k:ℝ) < n := by exact_mod_cast hsector
      change (4/3:ℝ)*((k:ℝ)*p/n) < (p:ℝ)/3000
      rw [←mul_div_assoc]
      exact (div_lt_iff₀ hnpos).mpr (by nlinarith only [mul_lt_mul_of_pos_right hs hpp])
    have hlim : (4/3:ℝ)*a ≤ ((p-1:ℕ):ℝ) := by
      rw [Nat.cast_sub hp1, Nat.cast_one]
      linarith only [hθ,hp2]
    have hstrict : b < p := by
      have hc : b ≤ p-1 := Nat.ceil_le.mpr hlim
      omega
    exact hstrict.le
  have hkpcut : 4*k*p ≤ 3*n*b := by
    have hc := mul_le_mul_of_nonneg_right hbc hnpos.le
    change ((4/3:ℝ)*((k:ℝ)*p/n))*n ≤ (b:ℝ)*n at hc
    rw [←mul_div_assoc,div_mul_cancel₀ _ hnpos.ne'] at hc
    exact_mod_cast (show 4*(k:ℝ)*p ≤ 3*(n:ℝ)*b by nlinarith only [hc])
  have hload := actual_load_lower_budget hp hb (alpha_front_sample_size hn hrank) hkpcut
  dsimp only at hload
  rw [accepted_probability_eq_realCount] at hload
  have hbmass := (baselinePairs_probability_bounds (n:=n) hb hble).1
  have hf : (249/250:ℝ)/d < f := calc
    _ = 1/d-(1/250:ℝ)/d := by ring
    _ ≤ (Nat.card (BaselinePairs n p b):ℝ)/((p.factorial:ℝ)*(p:ℝ)^n)-(1/250:ℝ)/d :=
      sub_le_sub_right hbmass _
    _ < _ := hload
  have hfa : f-α ≤ 2*((n:ℝ)*(1-1/(p:ℝ))^n) := by
    dsimp only [f,α]
    rw [←sub_div]
    exact (original_color_acceptance_error hn0 hp hk).2
  have hfα := hfa.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (alpha_front_transform_loss (n:=n) hp) hnpos.le) (by norm_num))
  have hrank' : 4*(p:ℝ)^2 ≤ n := by exact_mod_cast hrank
  have hble' : (b:ℝ) ≤ p := by exact_mod_cast hble
  have hscaled : d*(f-α) ≤ 15/(2*(n:ℝ)) := calc
    _ ≤ d*(2*((n:ℝ)*exp (-((n:ℝ)/p)))) := mul_le_mul_of_nonneg_left hfα hd.le
    _ ≤ _ := by
      simpa only [d,←mul_assoc] using color_load_transform_budget hnpos hpp hble' hrank'
  have hsmall : 15/(2*(n:ℝ)) ≤ 3/4000 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*n)).mpr
    linarith only [hn']
  have hαlow : (99/100:ℝ) ≤ α*d := by
    have hf' := (div_lt_iff₀ hd).mp hf
    exact le_of_lt (by nlinarith only [hf',hscaled.trans hsmall])
  have ha0 : 0 ≤ α := by
    exact nonneg_of_mul_nonneg_left ((by norm_num : (0:ℝ) ≤ 99/100).trans hαlow) hd
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (4/3:ℝ)*a by positivity)
  have hden : d ≤ 1+(8/3:ℝ)*a := by dsimp only [d,b]; linarith only [hceil]
  apply (div_le_iff₀ hnorm).mpr
  have h := hαlow.trans (mul_le_mul_of_nonneg_left hden ha0)
  nlinarith only [h]

/-- The load-only upper envelope at any size with at least 100 labels per
color. It supplies an upper bound for the original row at this size. -/
theorem original_front_acceptance_upper {n p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkn : k ≤ n) (hsize : 100*p ≤ n) :
    let a : ℝ := (k:ℝ)*p/n
    realCount n p k/(p:ℝ)^n ≤ 1 ∧ realCount n p k/(p:ℝ)^n ≤ 151/(100*a) := by
  let a : ℝ := (k:ℝ)*p/n
  let f : ℝ := realCount n p k/(p:ℝ)^n
  have hn : 0 < n := hk.trans_le hkn
  have hn' : (0:ℝ) < n := by positivity
  have hap : 0 < a := by dsimp [a]; positivity
  have hf1 : f ≤ 1 := (div_le_one (by positivity)).2 (realCount_bounds n p k).2
  change f ≤ 1 ∧ f ≤ 151/(100*a)
  refine ⟨hf1, ?_⟩
  by_cases ha : 3/2 ≤ a
  · let b : ℕ := ⌈(2/3:ℝ)*a⌉₊
    have hb : 0 < b := alpha_front_ceil_pos (by positivity : 0 < (2/3:ℝ)*a)
    have hbc : (2/3:ℝ)*a ≤ b := Nat.le_ceil _
    have hble : b ≤ p := by
      apply Nat.ceil_le.mpr
      have hk' : (k:ℝ) ≤ n := by exact_mod_cast hkn
      have hpa : a ≤ (p:ℝ) := by
        apply (div_le_iff₀ hn').mpr
        simpa only [mul_comm (p:ℝ) (n:ℝ)] using
          mul_le_mul_of_nonneg_right hk' (show 0≤(p:ℝ) by positivity)
      linarith only [hpa,hap]
    have hlarge : 3*n ≤ 2*k*p := by
      change (3/2:ℝ) ≤ (k:ℝ)*p/n at ha
      have ht := (le_div_iff₀ hn').mp ha
      exact_mod_cast (show 3*(n:ℝ) ≤ 2*(k:ℝ)*p by linarith only [ht])
    have hcut : 3*n*(b-1) ≤ 2*k*p := by
      have hc := Nat.ceil_lt_add_one (show 0 ≤ (2/3:ℝ)*a by positivity)
      change (b:ℝ) < _ at hc
      have hprev : ((b-1:ℕ):ℝ) ≤ (2/3:ℝ)*a := by
        rw [Nat.cast_sub hb, Nat.cast_one]
        linarith only [hc]
      change ((b-1:ℕ):ℝ) ≤ (2/3:ℝ)*((k:ℝ)*p/n) at hprev
      rw [←mul_div_assoc] at hprev
      have ht := (le_div_iff₀ hn').mp hprev
      exact_mod_cast (show 3*(n:ℝ)*((b-1:ℕ):ℝ) ≤ 2*(k:ℝ)*p by nlinarith only [ht])
    have hload := actual_load_upper_budget hp hb hsize hlarge hcut
    dsimp only at hload
    rw [accepted_probability_eq_realCount] at hload
    have hmass := (baselinePairs_probability_bounds (n:=n) hb hble).2
    have hfront : f ≤ 1/(b:ℝ)+(9/1000:ℝ)/a :=
      hload.trans (add_le_add_right hmass _)
    have hratio : 1/(b:ℝ) ≤ (3/2:ℝ)/a := by
      calc
        _ ≤ 1/((2/3:ℝ)*a) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hbc
        _ = _ := by field_simp [hap.ne']
    calc
      _ ≤ (3/2:ℝ)/a+(9/1000:ℝ)/a := hfront.trans (add_le_add_right hratio _)
      _ = (1509/1000:ℝ)/a := by ring
      _ ≤ _ := by
        rw [div_mul_eq_div_div]
        exact div_le_div_of_nonneg_right (by norm_num) hap.le
  · exact hf1.trans ((le_div_iff₀ (by positivity)).mpr (by linarith only [not_le.mp ha]))

theorem original_front_alpha_upper {n p k : ℕ} (hp : 0 < p) (hk : 2 ≤ k)
    (hkn : k ≤ n) (hsize : 100*p ≤ n) :
    let a : ℝ := (k:ℝ)*p/n
    (enumerator n k).coeff p/(p:ℝ)^n ≤ 1 ∧
      (enumerator n k).coeff p/(p:ℝ)^n ≤ 151/(100*a) := by
  have hk0 : 0 < k := by omega
  have he := (original_color_acceptance_error (hk0.trans_le hkn) hp hk).1
  rw [sub_div] at he
  have h := sub_nonneg.mp he
  have hf := original_front_acceptance_upper hp hk0 hkn hsize
  exact ⟨h.trans hf.1,h.trans hf.2⟩

#print axioms ColorAnchor.accepted_probability_eq_realCount
#print axioms ColorAnchor.realCount_one_color
#print axioms original_front_alpha_one
#print axioms original_front_alpha_lower
#print axioms original_front_acceptance_upper
#print axioms original_front_alpha_upper
end RepositoryQuotientAudit
