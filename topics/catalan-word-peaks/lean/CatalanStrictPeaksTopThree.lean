import CatalanStrictPeaksGeneratingFunction
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination

namespace CatalanStrictPeaks.TopThree

open Polynomial Finset
open scoped BigOperators

local notation "P" => ℝ[X]
local notation "S" => PowerSeries ℝ
local notation "PP" => PowerSeries P
local notation "SS" => PowerSeries S
local notation "s" => (PowerSeries.X : S)
local notation "Z" => (PowerSeries.X : PP)
local notation "z" => (PowerSeries.X : SS)
local notation "U" => PowerSeries.C P X

/-- Substitute 1 + X for the peak variable. -/
noncomputable def shift : P →+* P := Polynomial.eval₂RingHom Polynomial.C (1 + X)

private theorem shift_def (p : P) : shift p = p.comp (1 + X) := rfl

private theorem shift_X : shift X = 1 + X := by
  simp [shift_def]

theorem natDegree_shifted (n : ℕ) : ((C n).comp (X+1)).natDegree = rowDegree n := by
  rw [Polynomial.natDegree_comp, natDegree_C]
  have hx : (X + 1 : P).natDegree = 1 := Polynomial.natDegree_X_add_C 1
  rw [hx, mul_one]

private theorem coeff_shift_of_lt {n k : ℕ} (h : n ≤ 2*k) (hn : 0 < n) :
    (shift (C n)).coeff k = 0 := by
  rw [shift_def, add_comm]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [natDegree_shifted]
  unfold rowDegree
  omega

noncomputable def W : PP := PowerSeries.map shift FirstReturn.G - 1

private theorem W_eq : W = Z * (1 + W)^2 + U * Z^2 * W * (1 + W) := by
  have h := congrArg (PowerSeries.map shift) FirstReturn.generatingFunction_eq
  simp only [map_add, map_mul, map_sub, map_pow, map_one, PowerSeries.map_X,
    PowerSeries.map_C, shift_X, add_sub_cancel_left, sub_add_eq_sub_sub,
    sub_self, zero_sub, map_neg] at h
  have h' : PowerSeries.map shift FirstReturn.G =
      1 - U * Z^2 * PowerSeries.map shift FirstReturn.G +
      Z * (1 + U * Z) * (PowerSeries.map shift FirstReturn.G)^2 := by
    linear_combination h
  unfold W
  linear_combination h'

private theorem W_at_zero : PowerSeries.coeff P 0 W = 0 := by
  rw [W, map_sub, PowerSeries.coeff_map, FirstReturn.G, PowerSeries.coeff_mk,
    ← Recurrence.enumerate_X_eq_C, PowerSeries.coeff_one]
  simp [Recurrence.enumerate]

private theorem W_supported {n k : ℕ} (h : n ≤ 2*k) :
    (PowerSeries.coeff P n W).coeff k = 0 := by
  by_cases hn : n = 0
  · simp [hn, W_at_zero]
  · simp only [W, map_sub, PowerSeries.coeff_map, FirstReturn.G, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_neg hn, sub_zero]
    exact coeff_shift_of_lt h (Nat.pos_of_ne_zero hn)

/-- Transport the length grading to defect `n - 2*k`. -/
private noncomputable def shear (f : PP) : SS :=
  PowerSeries.mk fun r => PowerSeries.mk fun k => (PowerSeries.coeff P (r + 2*k) f).coeff k

private theorem shear_coeff (f : PP) (r k : ℕ) :
    PowerSeries.coeff ℝ k (PowerSeries.coeff S r (shear f)) =
      (PowerSeries.coeff P (r + 2*k) f).coeff k := by
  simp [shear]

private theorem shear_add (f g : PP) : shear (f + g) = shear f + shear g := by
  ext r k
  simp [shear_coeff]

private theorem shear_one : shear 1 = 1 := by
  ext r k
  simp only [shear_coeff, PowerSeries.coeff_one]
  by_cases hr : r = 0 <;> by_cases hk : k = 0 <;> simp_all

private theorem shear_Z : shear Z = z := by
  ext r k
  simp only [shear_coeff, PowerSeries.coeff_X]
  by_cases hr : r = 1 <;> by_cases hk : k = 0 <;> simp_all
  all_goals (try split_ifs) <;> first | omega | simp_all

private theorem shear_Z_sq_U : shear (U * Z^2) = PowerSeries.C S s := by
  ext r k
  simp only [shear_coeff, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C]
  split_ifs <;> simp only [PowerSeries.coeff_X, Polynomial.coeff_X, map_zero, Polynomial.coeff_zero]
  all_goals (try split_ifs) <;> first | rfl | omega

private def Supported (f : PP) : Prop :=
  ∀ n k, n < 2*k → (PowerSeries.coeff P n f).coeff k = 0

private theorem supported_add {f g : PP} (hf : Supported f) (hg : Supported g) :
    Supported (f + g) := by
  intro n k h
  simp [hf n k h, hg n k h]

private theorem supported_mul {f g : PP} (hf : Supported f) (hg : Supported g) :
    Supported (f * g) := by
  intro n k h
  simp only [PowerSeries.coeff_mul, Polynomial.finset_sum_coeff, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.mem_antidiagonal] at ha hb
  by_cases h' : a.1 < 2*b.1
  · rw [hf _ _ h', zero_mul]
  · rw [hg _ _ (by omega), mul_zero]

private theorem shear_mul {f g : PP} (hf : Supported f) (hg : Supported g) :
    shear (f * g) = shear f * shear g := by
  ext r k
  simp only [shear_coeff, PowerSeries.coeff_mul, Polynomial.finset_sum_coeff,
    Polynomial.coeff_mul, map_sum, ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero
    (fun (x : (ℕ × ℕ) × (ℕ × ℕ)) _ _ => ((x.1.1 - 2*x.2.1, x.1.2 - 2*x.2.2), x.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨⟨a,b⟩,⟨i,j⟩⟩ h hz
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h ⊢
    obtain ⟨ha, hb⟩ := h
    have h₁ : 2*i ≤ a := by
      by_contra! hi
      exact hz (by rw [hf _ _ hi, zero_mul])
    have h₂ : 2*j ≤ b := by
      by_contra! hj
      exact hz (by rw [hg _ _ hj, mul_zero])
    exact ⟨by omega, hb⟩
  · rintro ⟨⟨a,b⟩,⟨i,j⟩⟩ h hz ⟨⟨a',b'⟩,⟨i',j'⟩⟩ h' hz' he
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h h'
    simp only [Prod.mk.injEq] at he ⊢
    obtain ⟨⟨he₁,he₂⟩,rfl,rfl⟩ := he
    have h₁ : 2*i ≤ a := by
      by_contra! hi
      exact hz (by rw [hf _ _ hi, zero_mul])
    have h₂ : 2*j ≤ b := by
      by_contra! hj
      exact hz (by rw [hg _ _ hj, mul_zero])
    have h₁' : 2*i ≤ a' := by
      by_contra! hi
      exact hz' (by rw [hf _ _ hi, zero_mul])
    have h₂' : 2*j ≤ b' := by
      by_contra! hj
      exact hz' (by rw [hg _ _ hj, mul_zero])
    exact ⟨⟨by omega, by omega⟩,rfl,rfl⟩
  · rintro ⟨⟨a,b⟩,⟨i,j⟩⟩ h hz
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at h
    refine ⟨((a+2*i,b+2*j),(i,j)), ?_, hz, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_antidiagonal]
      exact ⟨by omega, h.2⟩
    · simp
  · rintro ⟨⟨a,b⟩,⟨i,j⟩⟩ h hz
    have h₁ : 2*i ≤ a := by
      by_contra! hi
      exact hz (by rw [hf _ _ hi, zero_mul])
    have h₂ : 2*j ≤ b := by
      by_contra! hj
      exact hz (by rw [hg _ _ hj, mul_zero])
    simp [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂]

private theorem supported_W : Supported W :=
  fun _ _ h => W_supported h.le

private theorem supported_one : Supported (1 : PP) := by
  intro n k h
  rw [PowerSeries.coeff_one]
  split_ifs with hn
  · rw [Polynomial.coeff_one, if_neg (by omega)]
  · exact Polynomial.coeff_zero _

private theorem supported_Z : Supported Z := by
  intro n k h
  rw [PowerSeries.coeff_X]
  split_ifs with hn
  · rw [Polynomial.coeff_one, if_neg (by omega)]
  · exact Polynomial.coeff_zero _

private theorem supported_Z_sq_U : Supported (U * Z^2) := by
  intro n k h
  rw [PowerSeries.coeff_C_mul_X_pow]
  split_ifs with hn
  · rw [Polynomial.coeff_X, if_neg (by omega)]
  · exact Polynomial.coeff_zero _

private noncomputable def F : SS := shear W

private theorem F_eq : F = z * (1 + F)^2 + PowerSeries.C S s * F * (1 + F) := by
  have h₁ := supported_add supported_one supported_W
  have h₂ := supported_mul supported_Z_sq_U supported_W
  have h₃ := supported_mul h₁ h₁
  unfold F
  calc
    _ = shear (Z * (1 + W)^2 + U * Z^2 * W * (1 + W)) := congrArg shear W_eq
    _ = _ := by
      rw [shear_add, pow_two, shear_mul supported_Z h₃, shear_mul h₁ h₁,
        shear_mul h₂ h₁, shear_mul supported_Z_sq_U supported_W, shear_add,
        shear_Z, shear_Z_sq_U, shear_one, pow_two]

/-- The geometric series in the mark for paired length. -/
noncomputable def A : S := PowerSeries.mk 1

private theorem A_mul_one_sub : A * (1 - s) = 1 :=
  PowerSeries.mk_one_mul_one_sub_eq_one ℝ

private theorem normalized_F :
    F = PowerSeries.C S A * z * (1 + F)^2 + PowerSeries.C S (A - 1) * F^2 := by
  have hAs : A * s = A - 1 := by linear_combination -A_mul_one_sub
  have hAS : PowerSeries.C S A * PowerSeries.C S s = PowerSeries.C S (A - 1) := by
    rw [← map_mul, hAs]
  have hA : PowerSeries.C S A - PowerSeries.C S (A - 1) = 1 := by
    rw [map_sub, map_one]
    ring
  have hF := congrArg (fun f : SS => PowerSeries.C S A * f) F_eq
  simp only at hF
  linear_combination hF +
    hAS * (F * (1 + F)) - hA * F

/-- The coefficient in defect r, still a formal series in the mark. -/
noncomputable def defect (r : ℕ) : S := PowerSeries.coeff S r F

private theorem defect_0 : defect 0 = 0 := by
  apply PowerSeries.ext
  intro k
  unfold defect F
  rw [shear_coeff, map_zero]
  exact W_supported (by omega)

private theorem coeff_shift_defect (r k : ℕ) (hr : 0 < r) :
    PowerSeries.coeff ℝ k (defect r) = (shift (C (r + 2*k))).coeff k := by
  unfold defect F
  rw [shear_coeff]
  have hn : r + 2 * k ≠ 0 := by omega
  simp only [W, map_sub, PowerSeries.coeff_map, FirstReturn.G, PowerSeries.coeff_mk,
    PowerSeries.coeff_one, if_neg hn, sub_zero]

private theorem coefficient_equation (n : ℕ) :
    defect (n+1) =
      A * PowerSeries.coeff S n ((1 + F)^2) +
      (A - 1) * PowerSeries.coeff S (n+1) (F^2) := by
  have h := congrArg (PowerSeries.coeff S (n+1)) normalized_F
  simpa only [defect, map_add, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul] using h

private theorem coeff_one_add_F (r : ℕ) :
    PowerSeries.coeff S r (1 + F) = (if r = 0 then 1 else 0) + defect r := by
  rw [map_add, PowerSeries.coeff_one, defect]

private theorem coeff_F_mul (r : ℕ) :
    PowerSeries.coeff S r (F^2) =
      ∑ a ∈ Finset.range (r+1), defect a * defect (r-a) := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private theorem coeff_one_add_F_mul (r : ℕ) :
    PowerSeries.coeff S r ((1 + F)^2) =
      ∑ a ∈ Finset.range (r+1),
        ((if a = 0 then 1 else 0) + defect a) *
        ((if r-a = 0 then 1 else 0) + defect (r-a)) := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_one_add_F]

theorem defect_1 : defect 1 = A := by
  have h := coefficient_equation 0
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0] at h
  linear_combination h

theorem defect_2 : defect 2 = A^2 + A^3 := by
  have h := coefficient_equation 1
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0, defect_1] at h
  linear_combination h

theorem defect_3 : defect 3 = A^3 + 2 * A^4 + 2 * A^5 := by
  have h := coefficient_equation 2
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0, defect_1, defect_2] at h
  linear_combination h

theorem defect_4 : defect 4 = A^4 + 3 * A^5 + 5 * A^6 + 5 * A^7 := by
  have h := coefficient_equation 3
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0, defect_1, defect_2, defect_3] at h
  linear_combination h

theorem defect_5 : defect 5 = A^5 + 4 * A^6 + 9 * A^7 + 14 * A^8 + 14 * A^9 := by
  have h := coefficient_equation 4
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0, defect_1, defect_2, defect_3, defect_4] at h
  linear_combination h

theorem defect_6 : defect 6 = A^6 + 5 * A^7 + 14 * A^8 + 28 * A^9 + 42 * A^10 + 42 * A^11 := by
  have h := coefficient_equation 5
  norm_num [coeff_one_add_F_mul, coeff_F_mul, Finset.sum_range_succ, defect_0, defect_1, defect_2, defect_3, defect_4, defect_5] at h
  linear_combination h

/-- Binomial coefficients in the geometric-power expansion. -/
def B (k d : ℕ) : ℝ := (Nat.choose (d+k) d : ℝ)

private theorem coeff_A_pow (k d : ℕ) :
    PowerSeries.coeff ℝ k (A^(d+1)) = B k d := by
  simp [A, B, PowerSeries.mk_one_pow_eq_mk_choose_add]

private theorem coeff_A (k : ℕ) :
    PowerSeries.coeff ℝ k A = 1 := by simp [A]

private theorem coeff_C_mul_A_pow (k d : ℕ) (c : ℝ) :
    PowerSeries.coeff ℝ k (PowerSeries.C ℝ c * A^(d+1)) = c * B k d := by
  rw [PowerSeries.coeff_C_mul, coeff_A_pow]

theorem coeff_shift_defect_1 (k : ℕ) :
    (shift (C (1 + 2*k))).coeff k = 1 := by
  rw [← coeff_shift_defect 1 k (by decide), defect_1]
  exact coeff_A k

theorem coeff_shift_defect_2 (k : ℕ) :
    (shift (C (2 + 2*k))).coeff k = B k 1 + B k 2 := by
  rw [← coeff_shift_defect 2 k (by decide), defect_2]
  simp only [map_add, coeff_A, ← map_ofNat (PowerSeries.C ℝ)]
  repeat first | rw [coeff_C_mul_A_pow] | rw [coeff_A_pow]

theorem coeff_shift_defect_3 (k : ℕ) :
    (shift (C (3 + 2*k))).coeff k = B k 2 + 2 * B k 3 + 2 * B k 4 := by
  rw [← coeff_shift_defect 3 k (by decide), defect_3]
  simp only [map_add, coeff_A, ← map_ofNat (PowerSeries.C ℝ)]
  repeat first | rw [coeff_C_mul_A_pow] | rw [coeff_A_pow]

theorem coeff_shift_defect_4 (k : ℕ) :
    (shift (C (4 + 2*k))).coeff k = B k 3 + 3 * B k 4 + 5 * B k 5 + 5 * B k 6 := by
  rw [← coeff_shift_defect 4 k (by decide), defect_4]
  simp only [map_add, coeff_A, ← map_ofNat (PowerSeries.C ℝ)]
  repeat first | rw [coeff_C_mul_A_pow] | rw [coeff_A_pow]

theorem coeff_shift_defect_5 (k : ℕ) :
    (shift (C (5 + 2*k))).coeff k = B k 4 + 4 * B k 5 + 9 * B k 6 + 14 * B k 7 + 14 * B k 8 := by
  rw [← coeff_shift_defect 5 k (by decide), defect_5]
  simp only [map_add, coeff_A, ← map_ofNat (PowerSeries.C ℝ)]
  repeat first | rw [coeff_C_mul_A_pow] | rw [coeff_A_pow]

theorem coeff_shift_defect_6 (k : ℕ) :
    (shift (C (6 + 2*k))).coeff k = B k 5 + 5 * B k 6 + 14 * B k 7 + 28 * B k 8 + 42 * B k 9 + 42 * B k 10 := by
  rw [← coeff_shift_defect 6 k (by decide), defect_6]
  simp only [map_add, coeff_A, ← map_ofNat (PowerSeries.C ℝ)]
  repeat first | rw [coeff_C_mul_A_pow] | rw [coeff_A_pow]

private theorem B_eq_ascFactorial (k d : ℕ) :
    B k d = ((k+1).ascFactorial d : ℝ) / (d.factorial : ℝ) := by
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero d), B, mul_comm, Nat.add_comm d k]
  exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose k d).symm

private theorem shift_eq_comp (p : P) : shift p = p.comp (X + 1) := by
  rw [shift_def, add_comm]

theorem coeff_odd_top (m : ℕ) :
    ((C (2*m+1)).comp (X+1)).coeff m = 1 := by
  rw [← shift_eq_comp, add_comm (2*m), coeff_shift_defect_1]

theorem coeff_even_top (m : ℕ) :
    ((C (2*m+2)).comp (X+1)).coeff m = ((m:ℝ)+1)*((m:ℝ)+4)/2 := by
  rw [← shift_eq_comp, add_comm (2*m), coeff_shift_defect_2]
  norm_num [B_eq_ascFactorial, Nat.factorial, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  ring

theorem coeff_odd_next (m : ℕ) (hm : 1 ≤ m) :
    ((C (2*m+1)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+4)*((m:ℝ)+5)/12 := by
  rw [← shift_eq_comp, show 2*m+1 = 3+2*(m-1) by omega, coeff_shift_defect_3]
  norm_num [B_eq_ascFactorial, Nat.factorial, Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_sub hm]
  ring

theorem coeff_even_next (m : ℕ) (hm : 1 ≤ m) :
    ((C (2*m+2)).comp (X+1)).coeff (m-1) =
      (m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)/144 := by
  rw [← shift_eq_comp, show 2*m+2 = 4+2*(m-1) by omega, coeff_shift_defect_4]
  norm_num [B_eq_ascFactorial, Nat.factorial, Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_sub hm]
  ring

theorem coeff_odd_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((C (2*m+1)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+5)*((m:ℝ)+6)*((m:ℝ)+7)*((m:ℝ)+8)/2880 := by
  rw [← shift_eq_comp, show 2*m+1 = 5+2*(m-2) by omega, coeff_shift_defect_5]
  norm_num [B_eq_ascFactorial, Nat.factorial, Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_sub hm]
  ring

theorem coeff_even_next_two (m : ℕ) (hm : 2 ≤ m) :
    ((C (2*m+2)).comp (X+1)).coeff (m-2) =
      ((m:ℝ)-1)*(m:ℝ)*((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+3)*((m:ℝ)+6)*((m:ℝ)+7)*
        ((m:ℝ)+8)*((m:ℝ)+9)*((m:ℝ)+10)/86400 := by
  rw [← shift_eq_comp, show 2*m+2 = 6+2*(m-2) by omega, coeff_shift_defect_6]
  norm_num [B_eq_ascFactorial, Nat.factorial, Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_sub hm]
  ring


end CatalanStrictPeaks.TopThree
