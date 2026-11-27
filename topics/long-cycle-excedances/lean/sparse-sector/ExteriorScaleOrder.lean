import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances

/-- Separation of adjacent positive centers orders every pair of closed boxes. -/
theorem exterior_scales_ordered {u : ℕ → ℝ} {H a b : ℕ}
    (hpos : ∀ h, 0 < h → h ≤ H → 0 < u h)
    (hstep : ∀ h, 0 < h → h+1 ≤ H → 20*u h < u (h+1))
    (ha : 0 < a) (hab : a < b) (hb : b ≤ H) :
    (9/8:ℝ)*u a ≤ (7/8:ℝ)*u b := by
  have hu : 0 < u a := hpos a ha (by omega)
  have hs := hstep a ha (by omega)
  have mono (d : ℕ) (hd : a+1 ≤ d) : d ≤ H → u (a+1) ≤ u d := by
    induction d, hd using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ d hd ih =>
      intro hH
      have hp := hpos d (by omega) (by omega)
      have hh := hstep d (by omega) hH
      exact (ih (by omega)).trans (by linarith)
  linarith [mono b hab hb]

#print axioms exterior_scales_ordered
end OpenMathResearch.LongCycleExcedances
