import LinearSlabs

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
namespace OpenMathResearch.LongCycleExcedances

/-- Numerators at scale 256 of the coarse signed star majorants. -/
def coarseStarNumerator (slab : Fin 9) : ℕ :=
  (![228, 278, 331, 368, 397, 421, 441, 453, 463] : Fin 9 → ℕ) slab

def coarseStarShape (slab : Fin 9) : ℚ :=
  linearShape (linearSlabK slab) 4 (linearSlabX slab)

end OpenMathResearch.LongCycleExcedances
