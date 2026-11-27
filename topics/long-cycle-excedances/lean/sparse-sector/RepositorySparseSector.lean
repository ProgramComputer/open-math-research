import ExteriorScaleOrder
import RepositoryOldFrontTails

set_option autoImplicit false
noncomputable section
namespace RepositoryQuotientAudit
open LongCycles LongCycleFinite Real OpenMathResearch.LongCycleExcedances

/-- Both original minimum-cycle excedance rows interlace in the large-size
logarithmic sector. Their reduced rows have complete strictly alternating
negative root lists with both outer roots belonging to the successor. -/
theorem original_sparse_sector_interlacing {n k : ℕ}
    (hn : 10000 ≤ n) (hk : 8 ≤ k)
    (hsize : 30*log (n:ℝ)+20 < (n:ℝ)/(200*(k:ℝ))) :
    StrictNegativeInterlacing (enumerator n k).divX (enumerator (n+1) k).divX (n-2) ∧
      WeakRealInterlacing (enumerator n k) (enumerator (n+1) k) := by
  have hk2 : 2 ≤ k := by omega
  have hs := front_sparse_of_large_size (by omega : 1 ≤ n) (by omega : 0 < k) hsize
  have tails (h : ℕ) (hh : 0 < h) (hH : h ≤ uniformJoinRank n) :=
    original_old_front_weighted_tails hn hk2 hs hh hH
  apply original_interlacing_of_exterior_weighted_envelopes hn (by omega) (by omega) hsize
  · intro i
    exact (tails (i.val+1) (Nat.succ_pos _) i.isLt).1
  · intro i j hij
    apply exterior_scales_ordered (u:=originalExteriorScale n k) (H:=uniformJoinRank n)
    · intro h hh hH
      exact div_pos (tails h hh hH).1.1 (tails h hh hH).1.2
    · intro h hh hH
      exact original_front_adjacent_gap hn hk2 hs hh hH
    · exact Nat.succ_pos _
    · exact Nat.succ_lt_succ (show i.val < j.val from hij)
    · exact j.isLt
  · intro i
    exact original_front_scale_cap hn hk2 hs (Nat.succ_pos i.val) i.isLt
  · intro i j hj
    exact (tails (i.val+1) (Nat.succ_pos _) i.isLt).2.1 j hj
  · intro i j hj
    exact (tails (i.val+1) (Nat.succ_pos _) i.isLt).2.2 j hj
  · exact original_exterior_near_lag hn hk hsize
  · intro i j hj
    exact original_far_front_weighted_lag hn hk2 hs (Nat.succ_pos i.val) i.isLt hj

#print axioms original_sparse_sector_interlacing
end RepositoryQuotientAudit
