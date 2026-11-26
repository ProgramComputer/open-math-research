import RibbonNarayana

/-! Check the exported result against the separately specified source and publication statements. -/

namespace AuditRibbonSource

open Ribbon.Source OpenMathResearch.MatroidKL

theorem original : NarayanaClaim (fun _ M => matroidZ M) := by
  intro n r M lower upper h
  obtain ⟨hCoeff, _, hRoots⟩ := h.narayana
  exact ⟨hCoeff, fun z hz => (hRoots z hz).1⟩

theorem published : PublishedNarayanaClaim (fun _ M => matroidZ M) :=
  fun _ _ _ _ _ h => h.narayana

theorem rankZero : RankZeroNarayanaClaim (fun _ M => matroidZ M) :=
  fun _ M h => matroidZ_of_rank_zero M h

end AuditRibbonSource
