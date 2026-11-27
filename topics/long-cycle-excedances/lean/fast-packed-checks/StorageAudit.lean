import PackedRowData
import PackedWordData

namespace OpenMathResearch.LongCycleExcedances.PackedShard

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 0 in
theorem listLastStep : packedStepOK 255 = true := by decide

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 0 in
theorem packedLastStep : StoredWords.packedStepOK 255 = true := by decide

#print axioms listLastStep
#print axioms packedLastStep
end OpenMathResearch.LongCycleExcedances.PackedShard
