import EulerianRootSpacing
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Basic

/-! The finite limiting cluster polynomial for positive powers of the Eulerian matrix,
in the positive root-modulus variable. -/

namespace EulerianCluster

open Polynomial EulerianRootSpacing
open scoped BigOperators

/-- Coefficients of this product are signed elementary symmetric functions. -/
noncomputable def input (as : List ℝ) : ℝ[X] :=
  (as.map (fun a => (1 : ℝ[X]) - C a * X)).prod

noncomputable def cluster (v : ℝ) : List ℝ → ℝ[X]
  | [] => 1
  | a :: as => spacingStep (cluster v as) a v

/-- The exact diagonal multiplier in the closed formula for the cluster. -/
theorem coeff_cluster (v : ℝ) (as : List ℝ) (k : ℕ) :
    (cluster v as).coeff k = (v⁻¹) ^ (k.choose 2) * (input as).coeff k := by
  induction as generalizing k with
  | nil =>
    cases k with
    | zero => simp [cluster, input]
    | succ k => simp [cluster, input, coeff_one]
  | cons a as ih =>
    have he : input (a :: as) = input as - C a * (X * input as) := by
      simp [input, sub_mul, mul_assoc]
    rw [he]
    simp only [cluster, spacingStep, mul_assoc, coeff_sub, coeff_C_mul]
    cases k with
    | zero => simp [ih]
    | succ k =>
      rw [coeff_X_mul, coeff_X_mul, comp_C_mul_X_coeff, ih, ih]
      have hk : (k+1).choose 2 = k + k.choose 2 := by
        simpa using Nat.choose_succ_succ k 1
      rw [hk, pow_add]
      ring

/-- Complete factorization, strict multiplicative spacing and positivity
of every limiting root modulus, for any list of positive parameters. -/
theorem factor_cluster {v : ℝ} (hv : 1 < v) (as : List ℝ)
    (ha : ∀ a ∈ as, 0 < a) :
    ∃ x : Fin as.length → ℝ, (∀ i, 0 < x i) ∧
      (∀ i j, i < j → v * x i < x j) ∧
      ∃ c : ℝ, 0 < c ∧ cluster v as = C c * rootProduct x := by
  induction as with
  | nil =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, 1, by norm_num, ?_⟩
    simp [cluster, rootProduct]
  | cons a as ih =>
    have hat : ∀ a' ∈ as, 0 < a' := fun a' h => ha _ (List.mem_cons_of_mem _ h)
    obtain ⟨x, hx, hs, c, hc, hfactor⟩ := ih hat
    obtain ⟨y, hy, _, hsep, _, t, ht, hprod⟩ :=
      spacingStep_roots x (ha a (by simp)) hv hx hs
    refine ⟨y, hy, hsep, c*t, mul_pos hc ht, ?_⟩
    change spacingStep (cluster v as) a v = _
    rw [hfactor, spacingStep_C_mul, hprod, ← mul_assoc, ← map_mul]

/-- The scale ratio for the h-th cluster and its p insertion weights,
indexed from zero here and from one in the manuscript. -/
noncomputable def scale (h : ℕ) : ℝ := ((h : ℝ) + 1) / h

noncomputable def weights (p h : ℕ) : List ℝ :=
  List.ofFn (fun i : Fin p =>
    (h : ℝ)⁻¹ ^ (p - 1 - i.val) * (scale h)⁻¹ ^ ((h-1)*i.val))

/-- Applied to the cluster at scale ((h+1)/h)^n for the p-th matrix power. -/
theorem matrixPowerCluster (p h : ℕ) (hh : 0 < h) :
    ∃ x : Fin p → ℝ, (∀ i, 0 < x i) ∧
      (∀ i j, i < j → scale h * x i < x j) ∧
      ∃ c : ℝ, 0 < c ∧ cluster (scale h) (weights p h) = C c * rootProduct x := by
  have hr : 0 < (h : ℝ) := by exact_mod_cast hh
  have hv : 1 < scale h := by
    rw [scale, lt_div_iff₀ hr]
    linarith
  have hpos : 0 < scale h := zero_lt_one.trans hv
  have hw : ∀ a ∈ weights p h, 0 < a := by
    intro a ha
    simp only [weights, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact mul_pos (pow_pos (inv_pos.mpr hr) _) (pow_pos (inv_pos.mpr hpos) _)
  have hlen : (weights p h).length = p := by simp [weights]
  have result := factor_cluster hv (weights p h) hw
  rw [hlen] at result
  exact result

end EulerianCluster
