import CoarseMomentCertificate

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
namespace OpenMathResearch.LongCycleExcedances

def coarseMomentFraction : Fin 8 → ℚ := ![1/48, 1/24, 1/12, 1/6, 1/3, 1/2, 3/4, 1]

def coarseZerothTable : Fin 8 → ℕ := ![580594377821416544, 415680153553609670, 301334825312970400, 223950916762327406, 174945243735568550, 157719939168769688, 148326192784329260, 145447503376568840]
def coarseFirstTable : Fin 8 → ℕ := ![2817052075887489070, 1361224857962553913, 634083749601318875, 272178622186254853, 95215937622986157, 41093421236354007, 12643366060083759, 3997375195126531]

theorem coarse_moment_tables (a : Fin 8) :
    coarseZerothUnits (coarseMomentFraction a/160) = coarseZerothTable a ∧
    coarseFirstUnits (coarseMomentFraction a/160) = coarseFirstTable a := by
  fin_cases a <;> decide +kernel

theorem coarse_moment_pair (a : Fin 8) {d : ℝ}
    (hd : ((coarseMomentFraction a / 160 : ℚ):ℝ) ≤ d) :
    zerothMomentBound d 31 ≤ (coarseZerothTable a:ℝ)/linearScale ∧
    firstMomentBound d 31 ≤ (coarseFirstTable a:ℝ)/linearScale := by
  have hc : (0:ℝ) < ((coarseMomentFraction a / 160 : ℚ):ℝ) := by
    fin_cases a <;> norm_num [coarseMomentFraction]
  obtain ⟨h0,h1⟩ := coarse_moment_tables a
  exact ⟨h0 ▸ coarse_zeroth_moment_cap hc hd, h1 ▸ coarse_first_moment_cap hc hd⟩

#print axioms coarse_moment_tables
#print axioms coarse_moment_pair
end OpenMathResearch.LongCycleExcedances
