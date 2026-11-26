import CatalanStrictPeaksGeneratingFunction
import Mathlib.Tactic.FieldSimp

/-!
# Exact scaled algebraic equation for the strict-peak series

In the analytic parameter the strict-peak variable is 1-c⁻² and the
length variable is rescaled by c. The discriminant identity below is a
formal-power-series statement.
-/

namespace CatalanStrictPeaks.FirstReturn

open Polynomial

local notation "R" => ℝ[X]
local notation "Z" => (PowerSeries.X : PowerSeries R)
local notation "x" => (PowerSeries.X : PowerSeries ℝ)

private noncomputable def specialization (c : ℝ) : PowerSeries R →+* PowerSeries ℝ :=
  (PowerSeries.rescale c).comp (PowerSeries.map (evalRingHom (1 - (c ^ 2)⁻¹)))

/-- The series whose nth coefficient is cⁿ Cₙ(1-c⁻²). -/
noncomputable def scaled (c : ℝ) : PowerSeries ℝ := specialization c G

theorem coeff_scaled (c : ℝ) (n : ℕ) :
    PowerSeries.coeff ℝ n (scaled c) = c ^ n * (C n).eval (1 - (c ^ 2)⁻¹) := by
  simp [scaled, specialization, PowerSeries.coeff_rescale, G]

private theorem rescale_const (c d : ℝ) :
    PowerSeries.rescale c (PowerSeries.C ℝ d) = PowerSeries.C ℝ d := by
  apply PowerSeries.ext
  intro n
  by_cases h : n = 0 <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, h]

private theorem specialization_C (c : ℝ) (p : R) :
    specialization c (PowerSeries.C R p) =
      PowerSeries.C ℝ (p.eval (1 - (c ^ 2)⁻¹)) := by
  simp [specialization, rescale_const]

private theorem specialization_X (c : ℝ) :
    specialization c Z = PowerSeries.C ℝ c * x := by
  simp [specialization]

/-- The quadratic equation in the rescaled length variable. -/
theorem scaled_eq (c : ℝ) (hc : c ≠ 0) :
    scaled c = 1 + x ^ 2 * scaled c +
      x * (PowerSeries.C ℝ c - x) * (scaled c) ^ 2 := by
  have h := congrArg (specialization c) generatingFunction_eq
  simp only [map_add, map_mul, map_pow, map_one, specialization_C, specialization_X,
    eval_sub, eval_one, eval_X] at h
  have hPos : 1 - (1 - (c ^ 2)⁻¹) = (c ^ 2)⁻¹ := by ring
  have hNeg : 1 - (c ^ 2)⁻¹ - 1 = -(c ^ 2)⁻¹ := by ring
  rw [hPos, hNeg, map_neg] at h
  have hcoeff : PowerSeries.C ℝ ((c ^ 2)⁻¹) * (PowerSeries.C ℝ c) ^ 2 = 1 := by
    rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), map_one]
  have hlinear :
      PowerSeries.C ℝ ((c ^ 2)⁻¹) * (PowerSeries.C ℝ c * x) ^ 2 = x ^ 2 := by
    calc
      _ = (PowerSeries.C ℝ ((c ^ 2)⁻¹) * (PowerSeries.C ℝ c) ^ 2) * x ^ 2 := by ring
      _ = _ := by rw [hcoeff, one_mul]
  have hquad :
      PowerSeries.C ℝ c * x * (1 + -PowerSeries.C ℝ ((c ^ 2)⁻¹) *
        (PowerSeries.C ℝ c * x)) = x * (PowerSeries.C ℝ c - x) := by
    calc
      _ = PowerSeries.C ℝ c * x -
          (PowerSeries.C ℝ ((c ^ 2)⁻¹) * (PowerSeries.C ℝ c) ^ 2) * x ^ 2 := by ring
      _ = _ := by rw [hcoeff, one_mul]; ring
  rw [hlinear, hquad] at h
  exact h

/-- The formal square-root branch selected by the constant term one. -/
noncomputable def discriminantBranch (c : ℝ) : PowerSeries ℝ :=
  1 - x ^ 2 - 2 * x * (PowerSeries.C ℝ c - x) * scaled c

theorem discriminantBranch_constant (c : ℝ) :
    PowerSeries.constantCoeff ℝ (discriminantBranch c) = 1 := by
  simp [discriminantBranch]

/-- The square-root branch has the exact quartic discriminant used in the
analytic argument. -/
theorem discriminantBranch_square (c : ℝ) (hc : c ≠ 0) :
    (discriminantBranch c) ^ 2 = (1 + x ^ 2) ^ 2 - 4 * PowerSeries.C ℝ c * x := by
  let a := x * (PowerSeries.C ℝ c - x)
  let f := scaled c
  have heq : a * f ^ 2 - (1 - x ^ 2) * f + 1 = 0 := by
    calc
      _ = (1 + x ^ 2 * f + a * f ^ 2) - f := by ring
      _ = 0 := by rw [← scaled_eq c hc]; exact sub_self _
  calc
    _ = (1 - x ^ 2) ^ 2 - 4 * a +
        4 * a * (a * f ^ 2 - (1 - x ^ 2) * f + 1) := by
      dsimp [discriminantBranch, a, f]
      ring
    _ = _ := by rw [heq]; dsimp [a]; ring

end CatalanStrictPeaks.FirstReturn
