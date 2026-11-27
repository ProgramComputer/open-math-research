import CutoffSingleSlabs

set_option autoImplicit false
namespace OpenMathResearch.LongCycleExcedances

/-- The nine closed integer aspect tests cover the full interval, with no
divisibility requirement at a shared endpoint. -/
theorem bounded_aspect_has_slab {n k : ℕ} (hl : 4*k ≤ n) (hu : n ≤ 48*k) :
    ∃ s : Fin 9, cutoffSlabLower s*k ≤ n ∧ n ≤ linearSlabX s*k := by
  by_contra! h
  have h0 : 4*k ≤ n → 6*k < n := h 0
  have h1 : 6*k ≤ n → 10*k < n := h 1
  have h2 : 10*k ≤ n → 16*k < n := h 2
  have h3 : 16*k ≤ n → 22*k < n := h 3
  have h4 : 22*k ≤ n → 28*k < n := h 4
  have h5 : 28*k ≤ n → 34*k < n := h 5
  have h6 : 34*k ≤ n → 40*k < n := h 6
  have h7 : 40*k ≤ n → 44*k < n := h 7
  have h8 : 44*k ≤ n → 48*k < n := h 8
  omega

#print axioms bounded_aspect_has_slab
end OpenMathResearch.LongCycleExcedances
