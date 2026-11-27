import HighSizeData

namespace OpenMathResearch.LongCycleExcedances.FastPointSamples
open IntegerSign RepositoryQuotientAudit

def sharpCheck (f : Pair) (p : Probe) : Bool :=
  packedPointCheck (size f p.upper) (row f p.upper).length
    (compactCoeff (row f p.upper)) p.num (2^p.bits) p.sign

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 10000 in
theorem control51 : probes51.all (sharpCheck pair51) = true := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 10000 in
theorem control160 : probes160.all (sharpCheck pair160) = true := by decide

#print axioms control51
#print axioms control160
end OpenMathResearch.LongCycleExcedances.FastPointSamples
