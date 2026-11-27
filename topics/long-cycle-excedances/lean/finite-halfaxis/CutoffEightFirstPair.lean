import CutoffEightRows
import HalfAxisDyadic

namespace RepositoryQuotientAudit.HalfAxisFirst

open Polynomial LongCycles LongCycleFinite

set_option maxRecDepth 10000

def firstWindows (i : Fin 15) : HalfAxisDyadicWindow :=
  match i.val with
  | 0 => ⟨⟨1, 32⟩, ⟨1, 31⟩⟩
  | 1 => ⟨⟨81, 25⟩, ⟨107, 25⟩⟩
  | 2 => ⟨⟨19, 17⟩, ⟨99, 19⟩⟩
  | 3 => ⟨⟨21, 14⟩, ⟨53, 15⟩⟩
  | 4 => ⟨⟨1243, 18⟩, ⟨173, 15⟩⟩
  | 5 => ⟨⟨97, 13⟩, ⟨65, 12⟩⟩
  | 6 => ⟨⟨111, 12⟩, ⟨73, 11⟩⟩
  | 7 => ⟨⟨27, 9⟩, ⟨65, 10⟩⟩
  | 8 => ⟨⟨11, 7⟩, ⟨51, 9⟩⟩
  | 9 => ⟨⟨9, 6⟩, ⟨83, 9⟩⟩
  | 10 => ⟨⟨113, 9⟩, ⟨1, 2⟩⟩
  | 11 => ⟨⟨37, 7⟩, ⟨21, 6⟩⟩
  | 12 => ⟨⟨105, 8⟩, ⟨1, 1⟩⟩
  | 13 => ⟨⟨37, 6⟩, ⟨41, 6⟩⟩
  | _ => ⟨⟨51, 6⟩, ⟨55, 6⟩⟩

private theorem checked32 :
    halfAxisDyadicOK 32 ((coefficientRow 32).map Int.ofNat)
      ((coefficientRow 33).map Int.ofNat) firstWindows = true := by decide

theorem original_weak_cutoff8_size32 :
    WeakRealInterlacing (enumerator 32 8) (enumerator 33 8) := by
  refine original_weak_of_checked_half_axis (n := 32) (k := 8) (by decide) (by decide)
    _ _ ?_ ?_ firstWindows checked32
  · exact ofCoeffs_eq_original_of_reads (width := 32) (by decide) (by decide) (by decide)
      _ (by decide) (rows_original 32 (by decide))
  · exact ofCoeffs_eq_original_of_reads (width := 32) (by decide) (by decide) (by decide)
      _ (by decide) (rows_original 33 (by decide))

end RepositoryQuotientAudit.HalfAxisFirst

#print axioms RepositoryQuotientAudit.HalfAxisFirst.original_weak_cutoff8_size32
