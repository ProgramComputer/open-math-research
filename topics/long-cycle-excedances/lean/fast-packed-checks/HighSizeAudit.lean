import HighSizeData

namespace OpenMathResearch.LongCycleExcedances.FastPointSamples

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 10000 in
theorem checks51 : probes51.all (check pair51) = true := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 10000 in
theorem checks160 : probes160.all (check pair160) = true := by decide

/-- All 80 strict signs at the 20 archived gaps of the size-1000 pair at cutoff 51. -/
theorem high_size_51_original (rows : ActualRows pair51 (by decide)) :
    ∀ p ∈ probes51, signedAt pair51 p :=
  fun p hp => signedAt_of_check pair51 (by decide) (by decide) rows p
    (List.all_eq_true.mp checks51 p hp)

/-- All eight strict signs at the two archived gaps of the size-1000 pair at cutoff 160. -/
theorem high_size_160_original (rows : ActualRows pair160 (by decide)) :
    ∀ p ∈ probes160, signedAt pair160 p :=
  fun p hp => signedAt_of_check pair160 (by decide) (by decide) rows p
    (List.all_eq_true.mp checks160 p hp)

#print axioms checks51
#print axioms checks160
#print axioms high_size_51_original
#print axioms high_size_160_original
end OpenMathResearch.LongCycleExcedances.FastPointSamples
