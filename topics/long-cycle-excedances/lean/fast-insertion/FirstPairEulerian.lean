import OriginalInsertionSigns

namespace RepositoryQuotientAudit
open LongCycleFinite

private theorem descentCoeffsSnapshot0 : descentCoeffs 0 = [1] := by
  rfl

private theorem descentCoeffsSnapshot1 : descentCoeffs 1 = [1] := by
  rw [descentCoeffs, descentCoeffsSnapshot0]
  decide

private theorem descentCoeffsSnapshot2 : descentCoeffs 2 = [1, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot1]
  decide

private theorem descentCoeffsSnapshot3 : descentCoeffs 3 = [1, 4, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot2]
  decide

private theorem descentCoeffsSnapshot4 : descentCoeffs 4 = [1, 11, 11, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot3]
  decide

private theorem descentCoeffsSnapshot5 : descentCoeffs 5 = [1, 26, 66, 26, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot4]
  decide

private theorem descentCoeffsSnapshot6 : descentCoeffs 6 = [1, 57, 302, 302, 57, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot5]
  decide

private theorem descentCoeffsSnapshot7 : descentCoeffs 7 = [1, 120, 1191, 2416, 1191, 120, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot6]
  decide

private theorem descentCoeffsSnapshot8 : descentCoeffs 8 = [1, 247, 4293, 15619, 15619, 4293, 247, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot7]
  decide

private theorem descentCoeffsSnapshot9 : descentCoeffs 9 = [1, 502, 14608, 88234, 156190, 88234, 14608, 502, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot8]
  decide

private theorem descentCoeffsSnapshot10 : descentCoeffs 10 = [1, 1013, 47840, 455192, 1310354, 1310354, 455192, 47840, 1013, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot9]
  decide

private theorem descentCoeffsSnapshot11 : descentCoeffs 11 = [1, 2036, 152637, 2203488, 9738114, 15724248, 9738114, 2203488, 152637, 2036, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot10]
  decide

theorem descentCoeffsSnapshot12 : descentCoeffs 12 = [1, 4083, 478271, 10187685, 66318474, 162512286, 162512286, 66318474, 10187685, 478271, 4083, 1] := by
  rw [descentCoeffs, descentCoeffsSnapshot11]
  decide

end RepositoryQuotientAudit

#print axioms RepositoryQuotientAudit.descentCoeffsSnapshot12
