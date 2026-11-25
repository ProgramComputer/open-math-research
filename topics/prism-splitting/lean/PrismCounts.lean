import PrismSplit

/-!
Certificate of every bounded-composition count used to construct the two prism numerators.
Each transition compares a closed convolution with a literal finite list. Rewriting a
proved transition avoids unfolding and recomputing earlier dynamic programming rows.
-/

namespace PrismSplit

set_option maxRecDepth 2500
set_option maxHeartbeats 650000

/-! Dilation 0, unsplit slice. -/

private def unsplit0Table0 : List Nat :=
  [1]

private theorem unsplit0Stage0 : countTable [] 0 = unsplit0Table0 := by rfl

private def unsplit0Table1 : List Nat :=
  [1]

private theorem unsplit0Transition1 :
    extendTable 0 0 unsplit0Table0 = unsplit0Table1 := by rfl

private theorem unsplit0Stage1 : countTable [0] 0 = unsplit0Table1 := by
  change extendTable 0 0 (countTable [] 0) = unsplit0Table1
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage0) unsplit0Transition1

private def unsplit0Table2 : List Nat :=
  [1]

private theorem unsplit0Transition2 :
    extendTable 0 0 unsplit0Table1 = unsplit0Table2 := by rfl

private theorem unsplit0Stage2 : countTable [0, 0] 0 = unsplit0Table2 := by
  change extendTable 0 0 (countTable [0] 0) = unsplit0Table2
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage1) unsplit0Transition2

private def unsplit0Table3 : List Nat :=
  [1]

private theorem unsplit0Transition3 :
    extendTable 0 0 unsplit0Table2 = unsplit0Table3 := by rfl

private theorem unsplit0Stage3 : countTable [0, 0, 0] 0 = unsplit0Table3 := by
  change extendTable 0 0 (countTable [0, 0] 0) = unsplit0Table3
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage2) unsplit0Transition3

private def unsplit0Table4 : List Nat :=
  [1]

private theorem unsplit0Transition4 :
    extendTable 0 0 unsplit0Table3 = unsplit0Table4 := by rfl

private theorem unsplit0Stage4 : countTable [0, 0, 0, 0] 0 = unsplit0Table4 := by
  change extendTable 0 0 (countTable [0, 0, 0] 0) = unsplit0Table4
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage3) unsplit0Transition4

private def unsplit0Table5 : List Nat :=
  [1]

private theorem unsplit0Transition5 :
    extendTable 0 0 unsplit0Table4 = unsplit0Table5 := by rfl

private theorem unsplit0Stage5 : countTable [0, 0, 0, 0, 0] 0 = unsplit0Table5 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0] 0) = unsplit0Table5
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage4) unsplit0Transition5

private def unsplit0Table6 : List Nat :=
  [1]

private theorem unsplit0Transition6 :
    extendTable 0 0 unsplit0Table5 = unsplit0Table6 := by rfl

private theorem unsplit0Stage6 : countTable [0, 0, 0, 0, 0, 0] 0 = unsplit0Table6 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0] 0) = unsplit0Table6
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage5) unsplit0Transition6

private def unsplit0Table7 : List Nat :=
  [1]

private theorem unsplit0Transition7 :
    extendTable 0 0 unsplit0Table6 = unsplit0Table7 := by rfl

private theorem unsplit0Stage7 : countTable [0, 0, 0, 0, 0, 0, 0] 0 = unsplit0Table7 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0] 0) = unsplit0Table7
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage6) unsplit0Transition7

private def unsplit0Table8 : List Nat :=
  [1]

private theorem unsplit0Transition8 :
    extendTable 0 0 unsplit0Table7 = unsplit0Table8 := by rfl

private theorem unsplit0Stage8 : countTable [0, 0, 0, 0, 0, 0, 0, 0] 0 = unsplit0Table8 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0] 0) = unsplit0Table8
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage7) unsplit0Transition8

private def unsplit0Table9 : List Nat :=
  [1]

private theorem unsplit0Transition9 :
    extendTable 0 0 unsplit0Table8 = unsplit0Table9 := by rfl

private theorem unsplit0Stage9 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = unsplit0Table9 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0] 0) = unsplit0Table9
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage8) unsplit0Transition9

private def unsplit0Table10 : List Nat :=
  [1]

private theorem unsplit0Transition10 :
    extendTable 0 0 unsplit0Table9 = unsplit0Table10 := by rfl

private theorem unsplit0Stage10 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = unsplit0Table10 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0, 0] 0) = unsplit0Table10
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage9) unsplit0Transition10

private def unsplit0Table11 : List Nat :=
  [1]

private theorem unsplit0Transition11 :
    extendTable 0 0 unsplit0Table10 = unsplit0Table11 := by rfl

private theorem unsplit0Stage11 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = unsplit0Table11 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0) = unsplit0Table11
  exact Eq.trans (congrArg (extendTable 0 0) unsplit0Stage10) unsplit0Transition11

private theorem unsplit0Exact : unsplitByCompositions 0 = unsplitLattice 0 := by
  change Int.ofNat ((countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0).getD 0 0) = _
  calc
    _ = 1 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 0 0) unsplit0Stage11) rfl)
    _ = _ := by decide

/-! Dilation 1, unsplit slice. -/

private def unsplit1Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0]

private theorem unsplit1Stage0 : countTable [] 6 = unsplit1Table0 := by rfl

private def unsplit1Table1 : List Nat :=
  [1, 1, 1, 0, 0, 0, 0]

private theorem unsplit1Transition1 :
    extendTable 6 2 unsplit1Table0 = unsplit1Table1 := by rfl

private theorem unsplit1Stage1 : countTable [2] 6 = unsplit1Table1 := by
  change extendTable 6 2 (countTable [] 6) = unsplit1Table1
  exact Eq.trans (congrArg (extendTable 6 2) unsplit1Stage0) unsplit1Transition1

private def unsplit1Table2 : List Nat :=
  [1, 2, 2, 1, 0, 0, 0]

private theorem unsplit1Transition2 :
    extendTable 6 1 unsplit1Table1 = unsplit1Table2 := by rfl

private theorem unsplit1Stage2 : countTable [1, 2] 6 = unsplit1Table2 := by
  change extendTable 6 1 (countTable [2] 6) = unsplit1Table2
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage1) unsplit1Transition2

private def unsplit1Table3 : List Nat :=
  [1, 3, 4, 3, 1, 0, 0]

private theorem unsplit1Transition3 :
    extendTable 6 1 unsplit1Table2 = unsplit1Table3 := by rfl

private theorem unsplit1Stage3 : countTable [1, 1, 2] 6 = unsplit1Table3 := by
  change extendTable 6 1 (countTable [1, 2] 6) = unsplit1Table3
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage2) unsplit1Transition3

private def unsplit1Table4 : List Nat :=
  [1, 4, 7, 7, 4, 1, 0]

private theorem unsplit1Transition4 :
    extendTable 6 1 unsplit1Table3 = unsplit1Table4 := by rfl

private theorem unsplit1Stage4 : countTable [1, 1, 1, 2] 6 = unsplit1Table4 := by
  change extendTable 6 1 (countTable [1, 1, 2] 6) = unsplit1Table4
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage3) unsplit1Transition4

private def unsplit1Table5 : List Nat :=
  [1, 5, 11, 14, 11, 5, 1]

private theorem unsplit1Transition5 :
    extendTable 6 1 unsplit1Table4 = unsplit1Table5 := by rfl

private theorem unsplit1Stage5 : countTable [1, 1, 1, 1, 2] 6 = unsplit1Table5 := by
  change extendTable 6 1 (countTable [1, 1, 1, 2] 6) = unsplit1Table5
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage4) unsplit1Transition5

private def unsplit1Table6 : List Nat :=
  [1, 6, 16, 25, 25, 16, 6]

private theorem unsplit1Transition6 :
    extendTable 6 1 unsplit1Table5 = unsplit1Table6 := by rfl

private theorem unsplit1Stage6 : countTable [1, 1, 1, 1, 1, 2] 6 = unsplit1Table6 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 2] 6) = unsplit1Table6
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage5) unsplit1Transition6

private def unsplit1Table7 : List Nat :=
  [1, 7, 22, 41, 50, 41, 22]

private theorem unsplit1Transition7 :
    extendTable 6 1 unsplit1Table6 = unsplit1Table7 := by rfl

private theorem unsplit1Stage7 : countTable [1, 1, 1, 1, 1, 1, 2] 6 = unsplit1Table7 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 2] 6) = unsplit1Table7
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage6) unsplit1Transition7

private def unsplit1Table8 : List Nat :=
  [1, 8, 29, 63, 91, 91, 63]

private theorem unsplit1Transition8 :
    extendTable 6 1 unsplit1Table7 = unsplit1Table8 := by rfl

private theorem unsplit1Stage8 : countTable [1, 1, 1, 1, 1, 1, 1, 2] 6 = unsplit1Table8 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 2] 6) = unsplit1Table8
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage7) unsplit1Transition8

private def unsplit1Table9 : List Nat :=
  [1, 9, 37, 92, 154, 182, 154]

private theorem unsplit1Transition9 :
    extendTable 6 1 unsplit1Table8 = unsplit1Table9 := by rfl

private theorem unsplit1Stage9 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 2] 6 = unsplit1Table9 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 2] 6) = unsplit1Table9
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage8) unsplit1Transition9

private def unsplit1Table10 : List Nat :=
  [1, 10, 46, 129, 246, 336, 336]

private theorem unsplit1Transition10 :
    extendTable 6 1 unsplit1Table9 = unsplit1Table10 := by rfl

private theorem unsplit1Stage10 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 2] 6 = unsplit1Table10 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1, 2] 6) = unsplit1Table10
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage9) unsplit1Transition10

private def unsplit1Table11 : List Nat :=
  [1, 11, 56, 175, 375, 582, 672]

private theorem unsplit1Transition11 :
    extendTable 6 1 unsplit1Table10 = unsplit1Table11 := by rfl

private theorem unsplit1Stage11 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] 6 = unsplit1Table11 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 2] 6) = unsplit1Table11
  exact Eq.trans (congrArg (extendTable 6 1) unsplit1Stage10) unsplit1Transition11

private theorem unsplit1Exact : unsplitByCompositions 1 = unsplitLattice 1 := by
  change Int.ofNat ((countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] 6).getD 6 0) = _
  calc
    _ = 672 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 6 0) unsplit1Stage11) rfl)
    _ = _ := by decide

/-! Dilation 2, unsplit slice. -/

private def unsplit2Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit2Stage0 : countTable [] 12 = unsplit2Table0 := by rfl

private def unsplit2Table1 : List Nat :=
  [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit2Transition1 :
    extendTable 12 4 unsplit2Table0 = unsplit2Table1 := by rfl

private theorem unsplit2Stage1 : countTable [4] 12 = unsplit2Table1 := by
  change extendTable 12 4 (countTable [] 12) = unsplit2Table1
  exact Eq.trans (congrArg (extendTable 12 4) unsplit2Stage0) unsplit2Transition1

private def unsplit2Table2 : List Nat :=
  [1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0]

private theorem unsplit2Transition2 :
    extendTable 12 2 unsplit2Table1 = unsplit2Table2 := by rfl

private theorem unsplit2Stage2 : countTable [2, 4] 12 = unsplit2Table2 := by
  change extendTable 12 2 (countTable [4] 12) = unsplit2Table2
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage1) unsplit2Transition2

private def unsplit2Table3 : List Nat :=
  [1, 3, 6, 8, 9, 8, 6, 3, 1, 0, 0, 0, 0]

private theorem unsplit2Transition3 :
    extendTable 12 2 unsplit2Table2 = unsplit2Table3 := by rfl

private theorem unsplit2Stage3 : countTable [2, 2, 4] 12 = unsplit2Table3 := by
  change extendTable 12 2 (countTable [2, 4] 12) = unsplit2Table3
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage2) unsplit2Transition3

private def unsplit2Table4 : List Nat :=
  [1, 4, 10, 17, 23, 25, 23, 17, 10, 4, 1, 0, 0]

private theorem unsplit2Transition4 :
    extendTable 12 2 unsplit2Table3 = unsplit2Table4 := by rfl

private theorem unsplit2Stage4 : countTable [2, 2, 2, 4] 12 = unsplit2Table4 := by
  change extendTable 12 2 (countTable [2, 2, 4] 12) = unsplit2Table4
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage3) unsplit2Transition4

private def unsplit2Table5 : List Nat :=
  [1, 5, 15, 31, 50, 65, 71, 65, 50, 31, 15, 5, 1]

private theorem unsplit2Transition5 :
    extendTable 12 2 unsplit2Table4 = unsplit2Table5 := by rfl

private theorem unsplit2Stage5 : countTable [2, 2, 2, 2, 4] 12 = unsplit2Table5 := by
  change extendTable 12 2 (countTable [2, 2, 2, 4] 12) = unsplit2Table5
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage4) unsplit2Transition5

private def unsplit2Table6 : List Nat :=
  [1, 6, 21, 51, 96, 146, 186, 201, 186, 146, 96, 51, 21]

private theorem unsplit2Transition6 :
    extendTable 12 2 unsplit2Table5 = unsplit2Table6 := by rfl

private theorem unsplit2Stage6 : countTable [2, 2, 2, 2, 2, 4] 12 = unsplit2Table6 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 4] 12) = unsplit2Table6
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage5) unsplit2Transition6

private def unsplit2Table7 : List Nat :=
  [1, 7, 28, 78, 168, 293, 428, 533, 573, 533, 428, 293, 168]

private theorem unsplit2Transition7 :
    extendTable 12 2 unsplit2Table6 = unsplit2Table7 := by rfl

private theorem unsplit2Stage7 : countTable [2, 2, 2, 2, 2, 2, 4] 12 = unsplit2Table7 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 4] 12) = unsplit2Table7
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage6) unsplit2Transition7

private def unsplit2Table8 : List Nat :=
  [1, 8, 36, 113, 274, 539, 889, 1254, 1534, 1639, 1534, 1254, 889]

private theorem unsplit2Transition8 :
    extendTable 12 2 unsplit2Table7 = unsplit2Table8 := by rfl

private theorem unsplit2Stage8 : countTable [2, 2, 2, 2, 2, 2, 2, 4] 12 = unsplit2Table8 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 4] 12) = unsplit2Table8
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage7) unsplit2Transition8

private def unsplit2Table9 : List Nat :=
  [1, 9, 45, 157, 423, 926, 1702, 2682, 3677, 4427, 4707, 4427, 3677]

private theorem unsplit2Transition9 :
    extendTable 12 2 unsplit2Table8 = unsplit2Table9 := by rfl

private theorem unsplit2Stage9 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 4] 12 = unsplit2Table9 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 4] 12) = unsplit2Table9
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage8) unsplit2Transition9

private def unsplit2Table10 : List Nat :=
  [1, 10, 55, 211, 625, 1506, 3051, 5310, 8061, 10786, 12811, 13561, 12811]

private theorem unsplit2Transition10 :
    extendTable 12 2 unsplit2Table9 = unsplit2Table10 := by rfl

private theorem unsplit2Stage10 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 4] 12 = unsplit2Table10 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2, 4] 12) = unsplit2Table10
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage9) unsplit2Transition10

private def unsplit2Table11 : List Nat :=
  [1, 11, 66, 276, 891, 2342, 5182, 9867, 16422, 24157, 31658, 37158, 39183]

private theorem unsplit2Transition11 :
    extendTable 12 2 unsplit2Table10 = unsplit2Table11 := by rfl

private theorem unsplit2Stage11 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4] 12 = unsplit2Table11 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 4] 12) = unsplit2Table11
  exact Eq.trans (congrArg (extendTable 12 2) unsplit2Stage10) unsplit2Transition11

private theorem unsplit2Exact : unsplitByCompositions 2 = unsplitLattice 2 := by
  change Int.ofNat ((countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4] 12).getD 12 0) = _
  calc
    _ = 39183 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 12 0) unsplit2Stage11) rfl)
    _ = _ := by decide

/-! Dilation 3, unsplit slice. -/

private def unsplit3Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit3Stage0 : countTable [] 18 = unsplit3Table0 := by rfl

private def unsplit3Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit3Transition1 :
    extendTable 18 6 unsplit3Table0 = unsplit3Table1 := by rfl

private theorem unsplit3Stage1 : countTable [6] 18 = unsplit3Table1 := by
  change extendTable 18 6 (countTable [] 18) = unsplit3Table1
  exact Eq.trans (congrArg (extendTable 18 6) unsplit3Stage0) unsplit3Transition1

private def unsplit3Table2 : List Nat :=
  [1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit3Transition2 :
    extendTable 18 3 unsplit3Table1 = unsplit3Table2 := by rfl

private theorem unsplit3Stage2 : countTable [3, 6] 18 = unsplit3Table2 := by
  change extendTable 18 3 (countTable [6] 18) = unsplit3Table2
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage1) unsplit3Transition2

private def unsplit3Table3 : List Nat :=
  [1, 3, 6, 10, 13, 15, 16, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0]

private theorem unsplit3Transition3 :
    extendTable 18 3 unsplit3Table2 = unsplit3Table3 := by rfl

private theorem unsplit3Stage3 : countTable [3, 3, 6] 18 = unsplit3Table3 := by
  change extendTable 18 3 (countTable [3, 6] 18) = unsplit3Table3
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage2) unsplit3Transition3

private def unsplit3Table4 : List Nat :=
  [1, 4, 10, 20, 32, 44, 54, 59, 59, 54, 44, 32, 20, 10, 4, 1, 0, 0, 0]

private theorem unsplit3Transition4 :
    extendTable 18 3 unsplit3Table3 = unsplit3Table4 := by rfl

private theorem unsplit3Stage4 : countTable [3, 3, 3, 6] 18 = unsplit3Table4 := by
  change extendTable 18 3 (countTable [3, 3, 6] 18) = unsplit3Table4
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage3) unsplit3Transition4

private def unsplit3Table5 : List Nat :=
  [1, 5, 15, 35, 66, 106, 150, 189, 216, 226, 216, 189, 150, 106, 66, 35, 15, 5, 1]

private theorem unsplit3Transition5 :
    extendTable 18 3 unsplit3Table4 = unsplit3Table5 := by rfl

private theorem unsplit3Stage5 : countTable [3, 3, 3, 3, 6] 18 = unsplit3Table5 := by
  change extendTable 18 3 (countTable [3, 3, 3, 6] 18) = unsplit3Table5
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage4) unsplit3Transition5

private def unsplit3Table6 : List Nat :=
  [1, 6, 21, 56, 121, 222, 357, 511, 661, 781, 847, 847, 781, 661, 511, 357, 222, 121, 56]

private theorem unsplit3Transition6 :
    extendTable 18 3 unsplit3Table5 = unsplit3Table6 := by rfl

private theorem unsplit3Stage6 : countTable [3, 3, 3, 3, 3, 6] 18 = unsplit3Table6 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 6] 18) = unsplit3Table6
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage5) unsplit3Transition6

private def unsplit3Table7 : List Nat :=
  [1, 7, 28, 84, 204, 420, 756, 1211, 1751, 2310, 2800, 3136, 3256, 3136, 2800, 2310, 1751, 1211,
   756]

private theorem unsplit3Transition7 :
    extendTable 18 3 unsplit3Table6 = unsplit3Table7 := by rfl

private theorem unsplit3Stage7 : countTable [3, 3, 3, 3, 3, 3, 6] 18 = unsplit3Table7 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 6] 18) = unsplit3Table7
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage6) unsplit3Transition7

private def unsplit3Table8 : List Nat :=
  [1, 8, 36, 120, 323, 736, 1464, 2591, 4138, 6028, 8072, 9997, 11502, 12328, 12328, 11502, 9997,
   8072, 6028]

private theorem unsplit3Transition8 :
    extendTable 18 3 unsplit3Table7 = unsplit3Table8 := by rfl

private theorem unsplit3Stage8 : countTable [3, 3, 3, 3, 3, 3, 3, 6] 18 = unsplit3Table8 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 6] 18) = unsplit3Table8
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage7) unsplit3Transition8

private def unsplit3Table9 : List Nat :=
  [1, 9, 45, 165, 487, 1215, 2643, 5114, 8929, 14221, 20829, 28235, 35599, 41899, 46155, 47660,
   46155, 41899, 35599]

private theorem unsplit3Transition9 :
    extendTable 18 3 unsplit3Table8 = unsplit3Table9 := by rfl

private theorem unsplit3Stage9 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 6] 18 = unsplit3Table9 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 6] 18) = unsplit3Table9
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage8) unsplit3Transition9

private def unsplit3Table10 : List Nat :=
  [1, 10, 55, 220, 706, 1912, 4510, 9459, 17901, 30907, 49093, 72214, 98884, 126562, 151888, 171313,
   181869, 181869, 171313]

private theorem unsplit3Transition10 :
    extendTable 18 3 unsplit3Table9 = unsplit3Table10 := by rfl

private theorem unsplit3Stage10 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 6] 18 = unsplit3Table10 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3, 6] 18) = unsplit3Table10
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage9) unsplit3Transition10

private def unsplit3Table11 : List Nat :=
  [1, 11, 66, 286, 991, 2893, 7348, 16587, 33782, 62777, 107360, 170115, 251098, 346753, 449548,
   548647, 631632, 686939, 706364]

private theorem unsplit3Transition11 :
    extendTable 18 3 unsplit3Table10 = unsplit3Table11 := by rfl

private theorem unsplit3Stage11 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6] 18 = unsplit3Table11 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 6] 18) = unsplit3Table11
  exact Eq.trans (congrArg (extendTable 18 3) unsplit3Stage10) unsplit3Transition11

private theorem unsplit3Exact : unsplitByCompositions 3 = unsplitLattice 3 := by
  change Int.ofNat ((countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6] 18).getD 18 0) = _
  calc
    _ = 706364 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 18 0) unsplit3Stage11) rfl)
    _ = _ := by decide

/-! Dilation 4, unsplit slice. -/

private def unsplit4Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit4Stage0 : countTable [] 24 = unsplit4Table0 := by rfl

private def unsplit4Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit4Transition1 :
    extendTable 24 8 unsplit4Table0 = unsplit4Table1 := by rfl

private theorem unsplit4Stage1 : countTable [8] 24 = unsplit4Table1 := by
  change extendTable 24 8 (countTable [] 24) = unsplit4Table1
  exact Eq.trans (congrArg (extendTable 24 8) unsplit4Stage0) unsplit4Transition1

private def unsplit4Table2 : List Nat :=
  [1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit4Transition2 :
    extendTable 24 4 unsplit4Table1 = unsplit4Table2 := by rfl

private theorem unsplit4Stage2 : countTable [4, 8] 24 = unsplit4Table2 := by
  change extendTable 24 4 (countTable [8] 24) = unsplit4Table2
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage1) unsplit4Transition2

private def unsplit4Table3 : List Nat :=
  [1, 3, 6, 10, 15, 19, 22, 24, 25, 24, 22, 19, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit4Transition3 :
    extendTable 24 4 unsplit4Table2 = unsplit4Table3 := by rfl

private theorem unsplit4Stage3 : countTable [4, 4, 8] 24 = unsplit4Table3 := by
  change extendTable 24 4 (countTable [4, 8] 24) = unsplit4Table3
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage2) unsplit4Transition3

private def unsplit4Table4 : List Nat :=
  [1, 4, 10, 20, 35, 53, 72, 90, 105, 114, 117, 114, 105, 90, 72, 53, 35, 20, 10, 4, 1, 0, 0, 0, 0]

private theorem unsplit4Transition4 :
    extendTable 24 4 unsplit4Table3 = unsplit4Table4 := by rfl

private theorem unsplit4Stage4 : countTable [4, 4, 4, 8] 24 = unsplit4Table4 := by
  change extendTable 24 4 (countTable [4, 4, 8] 24) = unsplit4Table4
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage3) unsplit4Transition4

private def unsplit4Table5 : List Nat :=
  [1, 5, 15, 35, 70, 122, 190, 270, 355, 434, 498, 540, 555, 540, 498, 434, 355, 270, 190, 122, 70,
   35, 15, 5, 1]

private theorem unsplit4Transition5 :
    extendTable 24 4 unsplit4Table4 = unsplit4Table5 := by rfl

private theorem unsplit4Stage5 : countTable [4, 4, 4, 4, 8] 24 = unsplit4Table5 := by
  change extendTable 24 4 (countTable [4, 4, 4, 8] 24) = unsplit4Table5
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage4) unsplit4Transition5

private def unsplit4Table6 : List Nat :=
  [1, 6, 21, 56, 126, 247, 432, 687, 1007, 1371, 1747, 2097, 2382, 2567, 2631, 2567, 2382, 2097,
   1747, 1371, 1007, 687, 432, 247, 126]

private theorem unsplit4Transition6 :
    extendTable 24 4 unsplit4Table5 = unsplit4Table6 := by rfl

private theorem unsplit4Stage6 : countTable [4, 4, 4, 4, 4, 8] 24 = unsplit4Table6 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 8] 24) = unsplit4Table6
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage5) unsplit4Transition6

private def unsplit4Table7 : List Nat :=
  [1, 7, 28, 84, 210, 456, 882, 1548, 2499, 3744, 5244, 6909, 8604, 10164, 11424, 12244, 12529,
   12244, 11424, 10164, 8604, 6909, 5244, 3744, 2499]

private theorem unsplit4Transition7 :
    extendTable 24 4 unsplit4Table6 = unsplit4Table7 := by rfl

private theorem unsplit4Stage7 : countTable [4, 4, 4, 4, 4, 4, 8] 24 = unsplit4Table7 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 8] 24) = unsplit4Table7
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage6) unsplit4Transition7

private def unsplit4Table8 : List Nat :=
  [1, 8, 36, 120, 330, 785, 1660, 3180, 5595, 9129, 13917, 19944, 27000, 34665, 42345, 49345, 54965,
   58605, 59865, 58605, 54965, 49345, 42345, 34665, 27000]

private theorem unsplit4Transition8 :
    extendTable 24 4 unsplit4Table7 = unsplit4Table8 := by rfl

private theorem unsplit4Stage8 : countTable [4, 4, 4, 4, 4, 4, 4, 8] 24 = unsplit4Table8 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 8] 24) = unsplit4Table8
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage7) unsplit4Transition8

private def unsplit4Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1279, 2931, 6075, 11550, 20349, 33481, 51765, 75585, 104655, 137871, 173299,
   208320, 239925, 265125, 281385, 287005, 281385, 265125, 239925, 208320]

private theorem unsplit4Transition9 :
    extendTable 24 4 unsplit4Table8 = unsplit4Table9 := by rfl

private theorem unsplit4Stage9 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 8] 24 = unsplit4Table9 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 8] 24) = unsplit4Table9
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage8) unsplit4Transition9

private def unsplit4Table10 : List Nat :=
  [1, 10, 55, 220, 715, 1993, 4915, 10945, 22330, 42184, 74386, 123220, 192730, 285835, 403357,
   543175, 699730, 864070, 1024540, 1168054, 1281760, 1354825, 1380025, 1354825, 1281760]

private theorem unsplit4Transition10 :
    extendTable 24 4 unsplit4Table9 = unsplit4Table10 := by rfl

private theorem unsplit4Stage10 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 8] 24 = unsplit4Table10 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4, 8] 24) = unsplit4Table10
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage9) unsplit4Transition10

private def unsplit4Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 2993, 7898, 18788, 40898, 82367, 154760, 273065, 454850, 718355, 1079528,
   1548317, 2124827, 2796167, 3534872, 4299569, 5038154, 5693249, 6209204, 6539489, 6653195]

private theorem unsplit4Transition11 :
    extendTable 24 4 unsplit4Table10 = unsplit4Table11 := by rfl

private theorem unsplit4Stage11 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8] 24 = unsplit4Table11 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 8] 24) = unsplit4Table11
  exact Eq.trans (congrArg (extendTable 24 4) unsplit4Stage10) unsplit4Transition11

private theorem unsplit4Exact : unsplitByCompositions 4 = unsplitLattice 4 := by
  change Int.ofNat ((countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8] 24).getD 24 0) = _
  calc
    _ = 6653195 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 24 0) unsplit4Stage11) rfl)
    _ = _ := by decide

/-! Dilation 5, unsplit slice. -/

private def unsplit5Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit5Stage0 : countTable [] 30 = unsplit5Table0 := by rfl

private def unsplit5Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit5Transition1 :
    extendTable 30 10 unsplit5Table0 = unsplit5Table1 := by rfl

private theorem unsplit5Stage1 : countTable [10] 30 = unsplit5Table1 := by
  change extendTable 30 10 (countTable [] 30) = unsplit5Table1
  exact Eq.trans (congrArg (extendTable 30 10) unsplit5Stage0) unsplit5Transition1

private def unsplit5Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit5Transition2 :
    extendTable 30 5 unsplit5Table1 = unsplit5Table2 := by rfl

private theorem unsplit5Stage2 : countTable [5, 10] 30 = unsplit5Table2 := by
  change extendTable 30 5 (countTable [10] 30) = unsplit5Table2
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage1) unsplit5Transition2

private def unsplit5Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 26, 30, 33, 35, 36, 35, 33, 30, 26, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0]

private theorem unsplit5Transition3 :
    extendTable 30 5 unsplit5Table2 = unsplit5Table3 := by rfl

private theorem unsplit5Stage3 : countTable [5, 5, 10] 30 = unsplit5Table3 := by
  change extendTable 30 5 (countTable [5, 10] 30) = unsplit5Table3
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage2) unsplit5Transition3

private def unsplit5Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 81, 108, 135, 160, 181, 195, 202, 202, 195, 181, 160, 135, 108, 81, 56, 35,
   20, 10, 4, 1, 0, 0, 0, 0, 0]

private theorem unsplit5Transition4 :
    extendTable 30 5 unsplit5Table3 = unsplit5Table4 := by rfl

private theorem unsplit5Stage4 : countTable [5, 5, 5, 10] 30 = unsplit5Table4 := by
  change extendTable 30 5 (countTable [5, 5, 10] 30) = unsplit5Table4
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage3) unsplit5Transition4

private def unsplit5Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 206, 310, 435, 575, 721, 860, 981, 1075, 1135, 1156, 1135, 1075, 981, 860,
   721, 575, 435, 310, 206, 126, 70, 35, 15, 5, 1]

private theorem unsplit5Transition5 :
    extendTable 30 5 unsplit5Table4 = unsplit5Table5 := by rfl

private theorem unsplit5Stage5 : countTable [5, 5, 5, 5, 10] 30 = unsplit5Table5 := by
  change extendTable 30 5 (countTable [5, 5, 5, 10] 30) = unsplit5Table5
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage4) unsplit5Transition5

private def unsplit5Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 457, 762, 1182, 1722, 2373, 3107, 3882, 4647, 5347, 5928, 6342, 6557,
   6557, 6342, 5928, 5347, 4647, 3882, 3107, 2373, 1722, 1182, 762, 457, 252]

private theorem unsplit5Transition6 :
    extendTable 30 5 unsplit5Table5 = unsplit5Table6 := by rfl

private theorem unsplit5Stage6 : countTable [5, 5, 5, 5, 5, 10] 30 = unsplit5Table6 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 10] 30) = unsplit5Table6
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage5) unsplit5Transition6

private def unsplit5Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 918, 1674, 2835, 4501, 6748, 9603, 13028, 16913, 21078, 25284, 29253,
   32703, 35378, 37073, 37654, 37073, 35378, 32703, 29253, 25284, 21078, 16913, 13028, 9603, 6748]

private theorem unsplit5Transition7 :
    extendTable 30 5 unsplit5Table6 = unsplit5Table7 := by rfl

private theorem unsplit5Stage7 : countTable [5, 5, 5, 5, 5, 5, 10] 30 = unsplit5Table7 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 10] 30) = unsplit5Table7
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage6) unsplit5Transition7

private def unsplit5Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1709, 3376, 6183, 10600, 17138, 26279, 38389, 53628, 71871, 92654,
   115159, 138259, 160609, 180769, 197345, 209134, 215259, 215259, 209134, 197345, 180769, 160609,
   138259, 115159, 92654]

private theorem unsplit5Transition8 :
    extendTable 30 5 unsplit5Table7 = unsplit5Table8 := by rfl

private theorem unsplit5Stage8 : countTable [5, 5, 5, 5, 5, 5, 5, 10] 30 = unsplit5Table8 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 10] 30) = unsplit5Table8
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage7) unsplit5Transition8

private def unsplit5Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 2995, 6363, 12510, 22990, 39798, 65285, 101965, 152217, 217905, 299959,
   397980, 509960, 632180, 759321, 884795, 1001275, 1101375, 1178375, 1226900, 1243476, 1226900,
   1178375, 1101375, 1001275, 884795]

private theorem unsplit5Transition9 :
    extendTable 30 5 unsplit5Table8 = unsplit5Table9 := by rfl

private theorem unsplit5Stage9 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 10] 30 = unsplit5Table9 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 10] 30) = unsplit5Table9
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage8) unsplit5Transition9

private def unsplit5Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 4996, 11350, 23815, 46640, 85943, 149941, 248911, 394765, 600160,
   877129, 1235311, 1679986, 2210201, 2817305, 3484195, 4185511, 4888906, 5557321, 6152041, 6636196,
   6978301, 7155401, 7155401, 6978301, 6636196]

private theorem unsplit5Transition10 :
    extendTable 30 5 unsplit5Table9 = unsplit5Table10 := by rfl

private theorem unsplit5Stage10 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 10] 30 = unsplit5Table10 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5, 10] 30) = unsplit5Table10
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage9) unsplit5Transition10

private def unsplit5Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 7998, 19338, 43098, 89518, 174746, 322685, 566600, 950015, 1526360,
   2356849, 3506217, 5036262, 6997552, 9420092, 12304127, 15612509, 19266104, 23143439, 27085279,
   30904170, 34398276, 37368166, 39634661, 41055641, 41539796]

private theorem unsplit5Transition11 :
    extendTable 30 5 unsplit5Table10 = unsplit5Table11 := by rfl

private theorem unsplit5Stage11 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 10] 30 = unsplit5Table11 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 10] 30) = unsplit5Table11
  exact Eq.trans (congrArg (extendTable 30 5) unsplit5Stage10) unsplit5Transition11

private theorem unsplit5Exact : unsplitByCompositions 5 = unsplitLattice 5 := by
  change Int.ofNat ((countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 10] 30).getD 30 0) = _
  calc
    _ = 41539796 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 30 0) unsplit5Stage11) rfl)
    _ = _ := by decide

/-! Dilation 6, unsplit slice. -/

private def unsplit6Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem unsplit6Stage0 : countTable [] 36 = unsplit6Table0 := by rfl

private def unsplit6Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem unsplit6Transition1 :
    extendTable 36 12 unsplit6Table0 = unsplit6Table1 := by rfl

private theorem unsplit6Stage1 : countTable [12] 36 = unsplit6Table1 := by
  change extendTable 36 12 (countTable [] 36) = unsplit6Table1
  exact Eq.trans (congrArg (extendTable 36 12) unsplit6Stage0) unsplit6Transition1

private def unsplit6Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem unsplit6Transition2 :
    extendTable 36 6 unsplit6Table1 = unsplit6Table2 := by rfl

private theorem unsplit6Stage2 : countTable [6, 12] 36 = unsplit6Table2 := by
  change extendTable 36 6 (countTable [12] 36) = unsplit6Table2
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage1) unsplit6Transition2

private def unsplit6Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 34, 39, 43, 46, 48, 49, 48, 46, 43, 39, 34, 28, 21, 15, 10, 6, 3, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit6Transition3 :
    extendTable 36 6 unsplit6Table2 = unsplit6Table3 := by rfl

private theorem unsplit6Stage3 : countTable [6, 6, 12] 36 = unsplit6Table3 := by
  change extendTable 36 6 (countTable [6, 12] 36) = unsplit6Table3
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage2) unsplit6Transition3

private def unsplit6Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 117, 153, 190, 226, 259, 287, 307, 319, 323, 319, 307, 287, 259, 226,
   190, 153, 117, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0]

private theorem unsplit6Transition4 :
    extendTable 36 6 unsplit6Table3 = unsplit6Table4 := by rfl

private theorem unsplit6Stage4 : countTable [6, 6, 6, 12] 36 = unsplit6Table4 := by
  change extendTable 36 6 (countTable [6, 6, 12] 36) = unsplit6Table4
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage3) unsplit6Transition4

private def unsplit6Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 326, 475, 655, 861, 1085, 1316, 1539, 1741, 1911, 2040, 2121, 2149,
   2121, 2040, 1911, 1741, 1539, 1316, 1085, 861, 655, 475, 326, 210, 126, 70, 35, 15, 5, 1]

private theorem unsplit6Transition5 :
    extendTable 36 6 unsplit6Table4 = unsplit6Table5 := by rfl

private theorem unsplit6Stage5 : countTable [6, 6, 6, 6, 12] 36 = unsplit6Table5 := by
  change extendTable 36 6 (countTable [6, 6, 6, 12] 36) = unsplit6Table5
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage4) unsplit6Transition5

private def unsplit6Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 787, 1257, 1897, 2723, 3738, 4928, 6257, 7672, 9108, 10493, 11753,
   12817, 13622, 14123, 14293, 14123, 13622, 12817, 11753, 10493, 9108, 7672, 6257, 4928, 3738,
   2723, 1897, 1257, 787, 462]

private theorem unsplit6Transition6 :
    extendTable 36 6 unsplit6Table5 = unsplit6Table6 := by rfl

private theorem unsplit6Stage6 : countTable [6, 6, 6, 6, 6, 12] 36 = unsplit6Table6 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 12] 36) = unsplit6Table6
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage5) unsplit6Transition6

private def unsplit6Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1710, 2961, 4837, 7504, 11116, 15792, 21587, 28472, 36323, 44919,
   53949, 63028, 71722, 79588, 86209, 91224, 94353, 95417, 94353, 91224, 86209, 79588, 71722, 63028,
   53949, 44919, 36323, 28472, 21587, 15792]

private theorem unsplit6Transition7 :
    extendTable 36 6 unsplit6Table6 = unsplit6Table7 := by rfl

private theorem unsplit6Stage7 : countTable [6, 6, 6, 6, 6, 6, 12] 36 = unsplit6Table7 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 12] 36) = unsplit6Table7
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage6) unsplit6Transition7

private def unsplit6Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3425, 6379, 11188, 18608, 29514, 44844, 65507, 92269, 125631,
   165713, 212158, 264070, 320000, 378001, 435738, 490639, 540073, 581541, 612866, 632368, 638989,
   632368, 612866, 581541, 540073, 490639, 435738, 378001, 320000, 264070]

private theorem unsplit6Transition8 :
    extendTable 36 6 unsplit6Table7 = unsplit6Table8 := by rfl

private theorem unsplit6Stage8 : countTable [6, 6, 6, 6, 6, 6, 6, 12] 36 = unsplit6Table8 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 12] 36) = unsplit6Table8
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage7) unsplit6Transition8

private def unsplit6Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6427, 12798, 23950, 42438, 71622, 115674, 179465, 268309, 387561,
   542086, 735636, 970192, 1245348, 1557842, 1901311, 2266319, 2640679, 3010062, 3358858, 3671226,
   3932214, 4128844, 4251071, 4292539, 4251071, 4128844, 3932214, 3671226, 3358858, 3010062]

private theorem unsplit6Transition9 :
    extendTable 36 6 unsplit6Table8 = unsplit6Table9 := by rfl

private theorem unsplit6Stage9 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 12] 36 = unsplit6Table9 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 12] 36) = unsplit6Table9
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage8) unsplit6Transition9

private def unsplit6Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11431, 24220, 48125, 90398, 161525, 275912, 452374, 714256,
   1089019, 1607155, 2300353, 3198923, 4328597, 5706974, 7339976, 9218734, 11317327, 13591753,
   15980419, 18406297, 20780669, 23008202, 24992954, 26644814, 27885823, 28655809, 28916797,
   28655809, 27885823, 26644814]

private theorem unsplit6Transition10 :
    extendTable 36 6 unsplit6Table9 = unsplit6Table10 := by rfl

private theorem unsplit6Stage10 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 12] 36 = unsplit6Table10 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6, 12] 36) = unsplit6Table10
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage9) unsplit6Transition10

private def unsplit6Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19438, 43648, 91718, 181896, 342706, 616616, 1063985, 1766810,
   2831609, 4390639, 6600594, 9637992, 13690677, 18945277, 25570997, 33700712, 43410884, 54702284,
   67483780, 81561480, 96635175, 112303401, 128077621, 143405108, 157699178, 170374568, 180885068,
   188760208, 193637829, 195289689]

private theorem unsplit6Transition11 :
    extendTable 36 6 unsplit6Table10 = unsplit6Table11 := by rfl

private theorem unsplit6Stage11 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 12] 36 = unsplit6Table11 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 12] 36) = unsplit6Table11
  exact Eq.trans (congrArg (extendTable 36 6) unsplit6Stage10) unsplit6Transition11

private theorem unsplit6Exact : unsplitByCompositions 6 = unsplitLattice 6 := by
  change Int.ofNat ((countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 12] 36).getD 36 0) = _
  calc
    _ = 195289689 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 36 0) unsplit6Stage11) rfl)
    _ = _ := by decide

/-! Dilation 7, unsplit slice. -/

private def unsplit7Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit7Stage0 : countTable [] 42 = unsplit7Table0 := by rfl

private def unsplit7Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit7Transition1 :
    extendTable 42 14 unsplit7Table0 = unsplit7Table1 := by rfl

private theorem unsplit7Stage1 : countTable [14] 42 = unsplit7Table1 := by
  change extendTable 42 14 (countTable [] 42) = unsplit7Table1
  exact Eq.trans (congrArg (extendTable 42 14) unsplit7Stage0) unsplit7Transition1

private def unsplit7Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit7Transition2 :
    extendTable 42 7 unsplit7Table1 = unsplit7Table2 := by rfl

private theorem unsplit7Stage2 : countTable [7, 14] 42 = unsplit7Table2 := by
  change extendTable 42 7 (countTable [14] 42) = unsplit7Table2
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage1) unsplit7Transition2

private def unsplit7Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 43, 49, 54, 58, 61, 63, 64, 63, 61, 58, 54, 49, 43, 36, 28, 21, 15,
   10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit7Transition3 :
    extendTable 42 7 unsplit7Table2 = unsplit7Table3 := by rfl

private theorem unsplit7Stage3 : countTable [7, 7, 14] 42 = unsplit7Table3 := by
  change extendTable 42 7 (countTable [7, 14] 42) = unsplit7Table3
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage2) unsplit7Transition3

private def unsplit7Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 162, 208, 256, 304, 350, 392, 428, 455, 473, 482, 482, 473, 455,
   428, 392, 350, 304, 256, 208, 162, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit7Transition4 :
    extendTable 42 7 unsplit7Table3 = unsplit7Table4 := by rfl

private theorem unsplit7Stage4 : countTable [7, 7, 7, 14] 42 = unsplit7Table4 := by
  change extendTable 42 7 (countTable [7, 7, 14] 42) = unsplit7Table4
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage3) unsplit7Transition4

private def unsplit7Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 491, 695, 941, 1225, 1540, 1876, 2220, 2555, 2866, 3140, 3366,
   3535, 3640, 3676, 3640, 3535, 3366, 3140, 2866, 2555, 2220, 1876, 1540, 1225, 941, 695, 491, 330,
   210, 126, 70, 35, 15, 5, 1]

private theorem unsplit7Transition5 :
    extendTable 42 7 unsplit7Table4 = unsplit7Table5 := by rfl

private theorem unsplit7Stage5 : countTable [7, 7, 7, 7, 14] 42 = unsplit7Table5 := by
  change extendTable 42 7 (countTable [7, 7, 7, 14] 42) = unsplit7Table5
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage4) unsplit7Transition5

private def unsplit7Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1282, 1972, 2898, 4088, 5558, 7308, 9318, 11543, 13918, 16363,
   18788, 21098, 23198, 24998, 26418, 27398, 27898, 27898, 27398, 26418, 24998, 23198, 21098, 18788,
   16363, 13918, 11543, 9318, 7308, 5558, 4088, 2898, 1972, 1282, 792]

private theorem unsplit7Transition6 :
    extendTable 42 7 unsplit7Table5 = unsplit7Table6 := by rfl

private theorem unsplit7Stage6 : countTable [7, 7, 7, 7, 7, 14] 42 = unsplit7Table6 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 14] 42) = unsplit7Table6
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage5) unsplit7Transition6

private def unsplit7Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 2997, 4963, 7840, 11872, 17304, 24360, 33216, 43967, 56603,
   70994, 86884, 103894, 121534, 139224, 156324, 172179, 186159, 197694, 206304, 211624, 213424,
   211624, 206304, 197694, 186159, 172179, 156324, 139224, 121534, 103894, 86884, 70994, 56603,
   43967, 33216]

private theorem unsplit7Transition7 :
    extendTable 42 7 unsplit7Table6 = unsplit7Table7 := by rfl

private theorem unsplit7Stage7 : countTable [7, 7, 7, 7, 7, 7, 14] 42 = unsplit7Table7 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 14] 42) = unsplit7Table7
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage6) unsplit7Transition7

private def unsplit7Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6428, 11384, 19196, 30984, 48078, 71976, 104268, 146519,
   200125, 266156, 345200, 437222, 541452, 656316, 779424, 907636, 1037192, 1163892, 1283312,
   1391042, 1482932, 1555332, 1605312, 1630827, 1630827, 1605312, 1555332, 1482932, 1391042,
   1283312, 1163892, 1037192, 907636, 779424, 656316]

private theorem unsplit7Transition8 :
    extendTable 42 7 unsplit7Table7 = unsplit7Table8 := by rfl

private theorem unsplit7Stage8 : countTable [7, 7, 7, 7, 7, 7, 7, 14] 42 = unsplit7Table8 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 14] 42) = unsplit7Table8
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage7) unsplit7Transition8

private def unsplit7Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12862, 24238, 43398, 74262, 122010, 193194, 295746, 438833,
   632530, 887302, 1213306, 1619544, 2112918, 2697258, 3372414, 4133531, 4970598, 5868334, 6806446,
   7760266, 8701746, 9600762, 10426650, 11149841, 11743476, 12184896, 12456916, 12548806, 12456916,
   12184896, 11743476, 11149841, 10426650, 9600762, 8701746]

private theorem unsplit7Transition9 :
    extendTable 42 7 unsplit7Table8 = unsplit7Table9 := by rfl

private theorem unsplit7Stage9 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 14] 42 = unsplit7Table9 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 14] 42) = unsplit7Table9
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage8) unsplit7Transition9

private def unsplit7Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24301, 48530, 91883, 165980, 287495, 479402, 772145,
   1204543, 1824211, 2687275, 3857183, 5402465, 7393373, 9897437, 12974105, 16668803, 21006871,
   25987903, 31581043, 37721765, 44310593, 51214097, 58268333, 65284643, 72057521, 78374083,
   84024553, 88813093, 92568263, 95152397, 96469223, 96469223, 95152397, 92568263, 88813093]

private theorem unsplit7Transition10 :
    extendTable 42 7 unsplit7Table9 = unsplit7Table10 := by rfl

private theorem unsplit7Stage10 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 14] 42 = unsplit7Table10 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7, 14] 42) = unsplit7Table10
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage9) unsplit7Transition10

private def unsplit7Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43748, 92268, 184096, 349856, 636636, 1114036, 1881176,
   3074279, 4874189, 7512934, 11278234, 16514719, 23620597, 33038632, 45240592, 60704852, 79887512,
   103188140, 130912000, 163231300, 200148520, 241465180, 286759408, 335375248, 386425898,
   438812078, 491255588, 542346916, 590604586, 634542886, 672743776, 703928356, 727023232,
   741217412, 746005952]

private theorem unsplit7Transition11 :
    extendTable 42 7 unsplit7Table10 = unsplit7Table11 := by rfl

private theorem unsplit7Stage11 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 14] 42 = unsplit7Table11 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 14] 42) = unsplit7Table11
  exact Eq.trans (congrArg (extendTable 42 7) unsplit7Stage10) unsplit7Transition11

private theorem unsplit7Exact : unsplitByCompositions 7 = unsplitLattice 7 := by
  change Int.ofNat ((countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 14] 42).getD 42 0) = _
  calc
    _ = 746005952 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 42 0) unsplit7Stage11) rfl)
    _ = _ := by decide

/-! Dilation 8, unsplit slice. -/

private def unsplit8Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit8Stage0 : countTable [] 48 = unsplit8Table0 := by rfl

private def unsplit8Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit8Transition1 :
    extendTable 48 16 unsplit8Table0 = unsplit8Table1 := by rfl

private theorem unsplit8Stage1 : countTable [16] 48 = unsplit8Table1 := by
  change extendTable 48 16 (countTable [] 48) = unsplit8Table1
  exact Eq.trans (congrArg (extendTable 48 16) unsplit8Stage0) unsplit8Transition1

private def unsplit8Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit8Transition2 :
    extendTable 48 8 unsplit8Table1 = unsplit8Table2 := by rfl

private theorem unsplit8Stage2 : countTable [8, 16] 48 = unsplit8Table2 := by
  change extendTable 48 8 (countTable [16] 48) = unsplit8Table2
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage1) unsplit8Transition2

private def unsplit8Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 53, 60, 66, 71, 75, 78, 80, 81, 80, 78, 75, 71, 66, 60, 53, 45,
   36, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit8Transition3 :
    extendTable 48 8 unsplit8Table2 = unsplit8Table3 := by rfl

private theorem unsplit8Stage3 : countTable [8, 8, 16] 48 = unsplit8Table3 := by
  change extendTable 48 8 (countTable [8, 16] 48) = unsplit8Table3
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage2) unsplit8Transition3

private def unsplit8Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 217, 274, 334, 395, 455, 512, 564, 609, 644, 669, 684, 689,
   684, 669, 644, 609, 564, 512, 455, 395, 334, 274, 217, 165, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0,
   0, 0, 0, 0, 0, 0]

private theorem unsplit8Transition4 :
    extendTable 48 8 unsplit8Table3 = unsplit8Table4 := by rfl

private theorem unsplit8Stage4 : countTable [8, 8, 8, 16] 48 = unsplit8Table4 := by
  change extendTable 48 8 (countTable [8, 8, 16] 48) = unsplit8Table4
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage3) unsplit8Transition4

private def unsplit8Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 711, 981, 1305, 1680, 2100, 2556, 3036, 3525, 4004, 4456,
   4866, 5221, 5510, 5724, 5856, 5901, 5856, 5724, 5510, 5221, 4866, 4456, 4004, 3525, 3036, 2556,
   2100, 1680, 1305, 981, 711, 495, 330, 210, 126, 70, 35, 15, 5, 1]

private theorem unsplit8Transition5 :
    extendTable 48 8 unsplit8Table4 = unsplit8Table5 := by rfl

private theorem unsplit8Stage5 : countTable [8, 8, 8, 8, 16] 48 = unsplit8Table5 := by
  change extendTable 48 8 (countTable [8, 8, 8, 16] 48) = unsplit8Table5
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage4) unsplit8Transition5

private def unsplit8Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 1997, 2973, 4263, 5908, 7938, 10368, 13194, 16389, 19898,
   23643, 27528, 31444, 35274, 38898, 42198, 45063, 47394, 49114, 50168, 50523, 50168, 49114, 47394,
   45063, 42198, 38898, 35274, 31444, 27528, 23643, 19898, 16389, 13194, 10368, 7938, 5908, 4263,
   2973, 1997, 1287]

private theorem unsplit8Transition6 :
    extendTable 48 8 unsplit8Table5 = unsplit8Table6 := by rfl

private theorem unsplit8Stage6 : countTable [8, 8, 8, 8, 8, 16] 48 = unsplit8Table6 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 16] 48) = unsplit8Table6
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage5) unsplit8Transition6

private def unsplit8Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 4999, 7966, 12208, 18060, 25872, 35988, 48720, 64317,
   82928, 104574, 129129, 156310, 185676, 216636, 248466, 280335, 311340, 340556, 367081, 390076,
   408800, 422640, 431136, 434001, 431136, 422640, 408800, 390076, 367081, 340556, 311340, 280335,
   248466, 216636, 185676, 156310, 129129, 104574, 82928, 64317]

private theorem unsplit8Transition7 :
    extendTable 48 8 unsplit8Table6 = unsplit8Table7 := by rfl

private theorem unsplit8Stage7 : countTable [8, 8, 8, 8, 8, 8, 16] 48 = unsplit8Table7 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 16] 48) = unsplit8Table7
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage6) unsplit8Transition7

private def unsplit8Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11433, 19392, 31572, 49548, 75210, 110736, 158532,
   221133, 301058, 400633, 521796, 665898, 833514, 1024278, 1236756, 1468371, 1715394, 1973022,
   2235529, 2496476, 2748966, 2985930, 3200430, 3385965, 3536766, 3648066, 3716310, 3739305,
   3716310, 3648066, 3536766, 3385965, 3200430, 2985930, 2748966, 2496476, 2235529, 1973022,
   1715394, 1468371]

private theorem unsplit8Transition8 :
    extendTable 48 8 unsplit8Table7 = unsplit8Table8 := by rfl

private theorem unsplit8Stage8 : countTable [8, 8, 8, 8, 8, 8, 8, 16] 48 = unsplit8Table8 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 16] 48) = unsplit8Table8
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage7) unsplit8Transition8

private def unsplit8Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24302, 43686, 75222, 124650, 199530, 309474, 466290,
   683991, 978614, 1367814, 1870218, 2504544, 3288510, 4237578, 5363598, 6673437, 8167698, 9839662,
   11674558, 13649238, 15732306, 17884722, 20060874, 22210083, 24278478, 26211150, 27954438,
   29458214, 30678048, 31577148, 32127984, 32313519, 32127984, 31577148, 30678048, 29458214,
   27954438, 26211150, 24278478, 22210083]

private theorem unsplit8Transition9 :
    extendTable 48 8 unsplit8Table8 = unsplit8Table9 := by rfl

private theorem unsplit8Stage9 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 16] 48 = unsplit8Table9 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 16] 48) = unsplit8Table9
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage8) unsplit8Transition9

private def unsplit8Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48611, 92288, 167465, 291950, 490985, 799172,
   1262459, 1940015, 2905759, 4249271, 6075803, 8505125, 11668985, 15707033, 20761157, 26968304,
   34452011, 43313059, 53619803, 65398823, 78626585, 93222797, 109046093, 125892578, 143497619,
   161541071, 179655847, 197439503, 214468313, 230313155, 244556417, 256809062, 266726963,
   274025633, 278492531, 279996307, 278492531, 274025633, 266726963, 256809062]

private theorem unsplit8Transition10 :
    extendTable 48 8 unsplit8Table9 = unsplit8Table10 := by rfl

private theorem unsplit8Stage10 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 16] 48 = unsplit8Table10 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8, 16] 48) = unsplit8Table10
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage9) unsplit8Transition10

private def unsplit8Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92368, 184646, 352056, 643786, 1134056, 1931226,
   3188680, 5117255, 7998704, 12199364, 18182879, 26520539, 37897574, 53113622, 73075607, 98781452,
   131293448, 171700748, 221071280, 280394300, 350515760, 432069572, 525408632, 630540053,
   747069368, 874158428, 1010501216, 1154320916, 1303390406, 1455076976, 1606410596, 1754173565,
   1895007950, 2025535964, 2142487424, 2242827884, 2323880912, 2383438232, 2419852040, 2432104685]

private theorem unsplit8Transition11 :
    extendTable 48 8 unsplit8Table10 = unsplit8Table11 := by rfl

private theorem unsplit8Stage11 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 16] 48 = unsplit8Table11 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 16] 48) = unsplit8Table11
  exact Eq.trans (congrArg (extendTable 48 8) unsplit8Stage10) unsplit8Transition11

private theorem unsplit8Exact : unsplitByCompositions 8 = unsplitLattice 8 := by
  change Int.ofNat ((countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 16] 48).getD 48 0) = _
  calc
    _ = 2432104685 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 48 0) unsplit8Stage11) rfl)
    _ = _ := by decide

/-! Dilation 9, unsplit slice. -/

private def unsplit9Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit9Stage0 : countTable [] 54 = unsplit9Table0 := by rfl

private def unsplit9Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit9Transition1 :
    extendTable 54 18 unsplit9Table0 = unsplit9Table1 := by rfl

private theorem unsplit9Stage1 : countTable [18] 54 = unsplit9Table1 := by
  change extendTable 54 18 (countTable [] 54) = unsplit9Table1
  exact Eq.trans (congrArg (extendTable 54 18) unsplit9Stage0) unsplit9Transition1

private def unsplit9Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit9Transition2 :
    extendTable 54 9 unsplit9Table1 = unsplit9Table2 := by rfl

private theorem unsplit9Stage2 : countTable [9, 18] 54 = unsplit9Table2 := by
  change extendTable 54 9 (countTable [18] 54) = unsplit9Table2
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage1) unsplit9Transition2

private def unsplit9Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 64, 72, 79, 85, 90, 94, 97, 99, 100, 99, 97, 94, 90, 85, 79,
   72, 64, 55, 45, 36, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0]

private theorem unsplit9Transition3 :
    extendTable 54 9 unsplit9Table2 = unsplit9Table3 := by rfl

private theorem unsplit9Stage3 : countTable [9, 9, 18] 54 = unsplit9Table3 := by
  change extendTable 54 9 (countTable [9, 18] 54) = unsplit9Table3
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage2) unsplit9Transition3

private def unsplit9Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 283, 352, 425, 500, 575, 648, 717, 780, 835, 879, 912,
   934, 945, 945, 934, 912, 879, 835, 780, 717, 648, 575, 500, 425, 352, 283, 220, 165, 120, 84, 56,
   35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit9Transition4 :
    extendTable 54 9 unsplit9Table3 = unsplit9Table4 := by rfl

private theorem unsplit9Stage4 : countTable [9, 9, 9, 18] 54 = unsplit9Table4 := by
  change extendTable 54 9 (countTable [9, 9, 18] 54) = unsplit9Table4
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage3) unsplit9Transition4

private def unsplit9Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 997, 1345, 1760, 2240, 2780, 3372, 4005, 4665, 5335,
   5994, 6623, 7205, 7725, 8170, 8529, 8793, 8955, 9010, 8955, 8793, 8529, 8170, 7725, 7205, 6623,
   5994, 5335, 4665, 4005, 3372, 2780, 2240, 1760, 1345, 997, 715, 495, 330, 210, 126, 70, 35, 15,
   5, 1]

private theorem unsplit9Transition5 :
    extendTable 54 9 unsplit9Table4 = unsplit9Table5 := by rfl

private theorem unsplit9Stage5 : countTable [9, 9, 9, 9, 18] 54 = unsplit9Table5 := by
  change extendTable 54 9 (countTable [9, 9, 9, 18] 54) = unsplit9Table5
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage4) unsplit9Transition5

private def unsplit9Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 2002, 2998, 4338, 6083, 8288, 10998, 14244, 18039, 22374,
   27214, 32493, 38119, 43979, 49944, 55874, 61623, 67044, 71994, 76339, 79959, 82758, 84664, 85629,
   85629, 84664, 82758, 79959, 76339, 71994, 67044, 61623, 55874, 49944, 43979, 38119, 32493, 27214,
   22374, 18039, 14244, 10998, 8288, 6083, 4338, 2998, 2002]

private theorem unsplit9Transition6 :
    extendTable 54 9 unsplit9Table5 = unsplit9Table6 := by rfl

private theorem unsplit9Stage6 : countTable [9, 9, 9, 9, 9, 18] 54 = unsplit9Table6 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 18] 54) = unsplit9Table6
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage5) unsplit9Transition6

private def unsplit9Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8002, 12334, 18396, 26628, 37500, 51492, 69069,
   90651, 116578, 147069, 182190, 221831, 265692, 313278, 363903, 416703, 470658, 524623, 577368,
   627633, 674178, 715828, 751513, 780303, 801438, 814353, 818698, 814353, 801438, 780303, 751513,
   715828, 674178, 627633, 577368, 524623, 470658, 416703, 363903, 313278, 265692, 221831, 182190,
   147069, 116578]

private theorem unsplit9Transition7 :
    extendTable 54 9 unsplit9Table6 = unsplit9Table7 := by rfl

private theorem unsplit9Stage7 : countTable [9, 9, 9, 9, 9, 9, 18] 54 = unsplit9Table7 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 18] 54) = unsplit9Table7
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage6) unsplit9Transition7

private def unsplit9Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11440, 19441, 31768, 50136, 76680, 113970, 165000,
   233145, 322080, 435655, 577719, 751907, 961404, 1208700, 1495350, 1821753, 2186964, 2588553,
   3022525, 3483315, 3963879, 4455867, 4949864, 5435685, 5902710, 6340245, 6737895, 7085935,
   7375665, 7599735, 7752405, 7829740, 7829740, 7752405, 7599735, 7375665, 7085935, 6737895,
   6340245, 5902710, 5435685, 4949864, 4455867, 3963879, 3483315, 3022525]

private theorem unsplit9Transition8 :
    extendTable 54 9 unsplit9Table7 = unsplit9Table8 := by rfl

private theorem unsplit9Stage8 : countTable [9, 9, 9, 9, 9, 9, 9, 18] 54 = unsplit9Table8 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 18] 54) = unsplit9Table8
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage7) unsplit9Transition8

private def unsplit9Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24310, 43750, 75510, 125610, 202170, 315810, 480018,
   711447, 1030095, 1459315, 2025594, 2758060, 3687696, 4846260, 6264930, 7972713, 9994677,
   12350085, 15050530, 18098190, 21484350, 25188310, 29176770, 33403755, 37811115, 42329607,
   46880538, 51377920, 55731060, 59847480, 63636006, 67009879, 69889755, 72206475, 73903500,
   74938920, 75286960, 74938920, 73903500, 72206475, 69889755, 67009879, 63636006, 59847480,
   55731060, 51377920]

private theorem unsplit9Transition9 :
    extendTable 54 9 unsplit9Table8 = unsplit9Table9 := by rfl

private theorem unsplit9Stage9 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 18] 54 = unsplit9Table9 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 18] 54) = unsplit9Table9
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage8) unsplit9Transition9

private def unsplit9Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620, 92369, 167870, 293435, 495440, 810755,
   1289486, 1997930, 3021590, 4468035, 6469319, 9183629, 12795815, 17516465, 23579225, 31236128,
   40750787, 52389425, 66409860, 83048735, 102507491, 124937741, 150426815, 178984310, 210530495,
   244887389, 281773250, 320801085, 361481615, 403230905, 445382561, 487204130, 527917115,
   566719835, 602812220, 635421533, 663827955, 687388955, 705561395, 717920390, 724174139,
   724174139, 717920390, 705561395, 687388955, 663827955]

private theorem unsplit9Transition10 :
    extendTable 54 9 unsplit9Table9 = unsplit9Table10 := by rfl

private theorem unsplit9Stage10 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 18] 54 = unsplit9Table10 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9, 18] 54) = unsplit9Table10
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage9) unsplit9Transition10

private def unsplit9Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92378, 184746, 352606, 645986, 1141206, 1951246,
   3238730, 5231655, 8241805, 12685530, 19106229, 28197489, 40825434, 58048464, 81132249, 111557622,
   151018923, 201410418, 264798688, 343379388, 439417560, 555171672, 692802672, 854270517,
   1041221787, 1254873048, 1495895511, 1764307171, 2059378926, 2379561096, 2722436166, 3084702555,
   3462192855, 3849928380, 4242210105, 4632744249, 5014798954, 5381386824, 5725466604, 6040156089,
   6318947667, 6555917676, 6745920951, 6884762511, 6969339246, 6997745668]

private theorem unsplit9Transition11 :
    extendTable 54 9 unsplit9Table10 = unsplit9Table11 := by rfl

private theorem unsplit9Stage11 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18] 54 = unsplit9Table11 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 18] 54) = unsplit9Table11
  exact Eq.trans (congrArg (extendTable 54 9) unsplit9Stage10) unsplit9Transition11

private theorem unsplit9Exact : unsplitByCompositions 9 = unsplitLattice 9 := by
  change Int.ofNat ((countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 18] 54).getD 54 0) = _
  calc
    _ = 6997745668 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 54 0) unsplit9Stage11) rfl)
    _ = _ := by decide

/-! Dilation 10, unsplit slice. -/

private def unsplit10Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit10Stage0 : countTable [] 60 = unsplit10Table0 := by rfl

private def unsplit10Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit10Transition1 :
    extendTable 60 20 unsplit10Table0 = unsplit10Table1 := by rfl

private theorem unsplit10Stage1 : countTable [20] 60 = unsplit10Table1 := by
  change extendTable 60 20 (countTable [] 60) = unsplit10Table1
  exact Eq.trans (congrArg (extendTable 60 20) unsplit10Stage0) unsplit10Transition1

private def unsplit10Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 10, 9, 8, 7, 6, 5, 4,
   3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0]

private theorem unsplit10Transition2 :
    extendTable 60 10 unsplit10Table1 = unsplit10Table2 := by rfl

private theorem unsplit10Stage2 : countTable [10, 20] 60 = unsplit10Table2 := by
  change extendTable 60 10 (countTable [20] 60) = unsplit10Table2
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage1) unsplit10Transition2

private def unsplit10Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 76, 85, 93, 100, 106, 111, 115, 118, 120, 121, 120, 118,
   115, 111, 106, 100, 93, 85, 76, 66, 55, 45, 36, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit10Transition3 :
    extendTable 60 10 unsplit10Table2 = unsplit10Table3 := by rfl

private theorem unsplit10Stage3 : countTable [10, 10, 20] 60 = unsplit10Table3 := by
  change extendTable 60 10 (countTable [10, 20] 60) = unsplit10Table3
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage2) unsplit10Transition3

private def unsplit10Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 361, 443, 530, 620, 711, 801, 888, 970, 1045, 1111,
   1165, 1207, 1237, 1255, 1261, 1255, 1237, 1207, 1165, 1111, 1045, 970, 888, 801, 711, 620, 530,
   443, 361, 286, 220, 165, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem unsplit10Transition4 :
    extendTable 60 10 unsplit10Table3 = unsplit10Table4 := by rfl

private theorem unsplit10Stage4 : countTable [10, 10, 10, 20] 60 = unsplit10Table4 := by
  change extendTable 60 10 (countTable [10, 10, 20] 60) = unsplit10Table4
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage3) unsplit10Transition4

private def unsplit10Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1361, 1800, 2320, 2920, 3596, 4341, 5145, 5995,
   6875, 7766, 8645, 9491, 10285, 11010, 11651, 12195, 12631, 12950, 13145, 13211, 13145, 12950,
   12631, 12195, 11651, 11010, 10285, 9491, 8645, 7766, 6875, 5995, 5145, 4341, 3596, 2920, 2320,
   1800, 1361, 1001, 715, 495, 330, 210, 126, 70, 35, 15, 5, 1]

private theorem unsplit10Transition5 :
    extendTable 60 10 unsplit10Table4 = unsplit10Table5 := by rfl

private theorem unsplit10Stage5 : countTable [10, 10, 10, 10, 20] 60 = unsplit10Table5 := by
  change extendTable 60 10 (countTable [10, 10, 10, 20] 60) = unsplit10Table5
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage4) unsplit10Transition5

private def unsplit10Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 2002, 3003, 4363, 6158, 8463, 11348, 14874, 19089, 24024,
   29689, 36069, 43120, 50764, 58894, 67379, 76069, 84800, 93399, 101689, 109494, 116644, 122980,
   128359, 132664, 135804, 137714, 138355, 137714, 135804, 132664, 128359, 122980, 116644, 109494,
   101689, 93399, 84800, 76069, 67379, 58894, 50764, 43120, 36069, 29689, 24024, 19089, 14874,
   11348, 8463, 6158, 4363, 3003]

private theorem unsplit10Transition6 :
    extendTable 60 10 unsplit10Table5 = unsplit10Table6 := by rfl

private theorem unsplit10Stage6 : countTable [10, 10, 10, 10, 10, 20] 60 = unsplit10Table6 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 20] 60) = unsplit10Table6
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage5) unsplit10Transition6

private def unsplit10Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8008, 12370, 18522, 26964, 38256, 53004, 71841,
   95403, 124300, 159082, 200200, 247961, 302492, 363713, 431319, 504771, 583296, 665896, 751366,
   838321, 925232, 1010471, 1092371, 1169281, 1239616, 1301902, 1354816, 1397221, 1428196, 1447061,
   1453397, 1447061, 1428196, 1397221, 1354816, 1301902, 1239616, 1169281, 1092371, 1010471, 925232,
   838321, 751366, 665896, 583296, 504771, 431319, 363713, 302492, 247961, 200200]

private theorem unsplit10Transition7 :
    extendTable 60 10 unsplit10Table6 = unsplit10Table7 := by rfl

private theorem unsplit10Stage7 : countTable [10, 10, 10, 10, 10, 10, 20] 60 = unsplit10Table7 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 20] 60) = unsplit10Table7
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage6) unsplit10Transition7

private def unsplit10Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11440, 19448, 31817, 50332, 77268, 115440, 168234,
   239613, 334092, 456676, 612755, 807950, 1047903, 1338025, 1683216, 2087571, 2554086, 3084378,
   3678433, 4334396, 5048417, 5814567, 6624838, 7469248, 8336037, 9211940, 10082523, 10932568,
   11746493, 12508793, 13204488, 13819564, 14341393, 14759118, 15063968, 15249503, 15311789,
   15249503, 15063968, 14759118, 14341393, 13819564, 13204488, 12508793, 11746493, 10932568,
   10082523, 9211940, 8336037, 7469248, 6624838, 5814567]

private theorem unsplit10Transition8 :
    extendTable 60 10 unsplit10Table7 = unsplit10Table8 := by rfl

private theorem unsplit10Stage8 : countTable [10, 10, 10, 10, 10, 10, 10, 20] 60 = unsplit10Table8 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 20] 60) = unsplit10Table8
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage7) unsplit10Transition8

private def unsplit10Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24310, 43758, 75574, 125898, 203130, 318450, 486354,
   725175, 1057551, 1510795, 2117115, 2913625, 3942080, 5248288, 6881172, 8891475, 11330121,
   14246265, 17685085, 21685389, 26277130, 31478942, 37295830, 43717175, 50715187, 58243911,
   66238863, 74617345, 83279460, 92109820, 100979912, 109751059, 118277885, 126412165, 134006885,
   140920351, 147020200, 152187180, 156318580, 159331205, 161163805, 161778881, 161163805,
   159331205, 156318580, 152187180, 147020200, 140920351, 134006885, 126412165, 118277885,
   109751059]

private theorem unsplit10Transition9 :
    extendTable 60 10 unsplit10Table8 = unsplit10Table9 := by rfl

private theorem unsplit10Stage9 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 20] 60 = unsplit10Table9 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 20] 60) = unsplit10Table9
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage8) unsplit10Transition9

private def unsplit10Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620, 92378, 167951, 293840, 496925, 815210,
   1301069, 2024957, 3079505, 4583865, 6688110, 9577425, 13475747, 18648461, 25403735, 34092080,
   45103751, 58863662, 75823572, 96451410, 121217745, 150579572, 184961777, 224736872, 270203771,
   321566510, 378913898, 442201122, 511234317, 585659052, 664953575, 748427504, 835226447,
   924342782, 1014632492, 1104837656, 1193613945, 1279562262, 1361263497, 1437315242, 1506369227,
   1567168196, 1618580942, 1659634262, 1689540677, 1707720972, 1713820821, 1707720972, 1689540677,
   1659634262, 1618580942, 1567168196]

private theorem unsplit10Transition10 :
    extendTable 60 10 unsplit10Table9 = unsplit10Table10 := by rfl

private theorem unsplit10Stage10 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 20] 60 = unsplit10Table10 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10, 20] 60) = unsplit10Table10
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage9) unsplit10Transition10

private def unsplit10Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92378, 184756, 352706, 646536, 1143406, 1958396,
   3258750, 5281705, 8356205, 12928630, 19592430, 29121235, 42504604, 60985114, 86095009, 119690164,
   163978705, 221541298, 295339913, 388711818, 505345698, 649237160, 824621512, 1035882637,
   1287437947, 1583600722, 1928422540, 2325519911, 2777890566, 3287726046, 3856228211, 4483437970,
   5168084845, 5907465850, 6697361470, 7531995355, 8404042790, 9304691154, 10223753529, 11149834454,
   12070544629, 12972759250, 13842912688, 14667320503, 15432518398, 16125606878, 16734590043,
   17248697070, 17658675485, 17957046250, 18138311950, 18199110919]

private theorem unsplit10Transition11 :
    extendTable 60 10 unsplit10Table10 = unsplit10Table11 := by rfl

private theorem unsplit10Stage11 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20] 60 = unsplit10Table11 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 20] 60) = unsplit10Table11
  exact Eq.trans (congrArg (extendTable 60 10) unsplit10Stage10) unsplit10Transition11

private theorem unsplit10Exact : unsplitByCompositions 10 = unsplitLattice 10 := by
  change Int.ofNat ((countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20] 60).getD 60 0) = _
  calc
    _ = 18199110919 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 60 0) unsplit10Stage11) rfl)
    _ = _ := by decide

theorem unsplitSamplesAgree (q : Nat) (hq : q ≤ 10) :
    unsplitByCompositions q = unsplitLattice q := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact unsplit0Exact
  · exact unsplit1Exact
  · exact unsplit2Exact
  · exact unsplit3Exact
  · exact unsplit4Exact
  · exact unsplit5Exact
  · exact unsplit6Exact
  · exact unsplit7Exact
  · exact unsplit8Exact
  · exact unsplit9Exact
  · exact unsplit10Exact

/-! Dilation 0, split slice. -/

private def split0Table0 : List Nat :=
  [1]

private theorem split0Stage0 : countTable [] 0 = split0Table0 := by rfl

private def split0Table1 : List Nat :=
  [1]

private theorem split0Transition1 :
    extendTable 0 0 split0Table0 = split0Table1 := by rfl

private theorem split0Stage1 : countTable [0] 0 = split0Table1 := by
  change extendTable 0 0 (countTable [] 0) = split0Table1
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage0) split0Transition1

private def split0Table2 : List Nat :=
  [1]

private theorem split0Transition2 :
    extendTable 0 0 split0Table1 = split0Table2 := by rfl

private theorem split0Stage2 : countTable [0, 0] 0 = split0Table2 := by
  change extendTable 0 0 (countTable [0] 0) = split0Table2
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage1) split0Transition2

private def split0Table3 : List Nat :=
  [1]

private theorem split0Transition3 :
    extendTable 0 0 split0Table2 = split0Table3 := by rfl

private theorem split0Stage3 : countTable [0, 0, 0] 0 = split0Table3 := by
  change extendTable 0 0 (countTable [0, 0] 0) = split0Table3
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage2) split0Transition3

private def split0Table4 : List Nat :=
  [1]

private theorem split0Transition4 :
    extendTable 0 0 split0Table3 = split0Table4 := by rfl

private theorem split0Stage4 : countTable [0, 0, 0, 0] 0 = split0Table4 := by
  change extendTable 0 0 (countTable [0, 0, 0] 0) = split0Table4
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage3) split0Transition4

private def split0Table5 : List Nat :=
  [1]

private theorem split0Transition5 :
    extendTable 0 0 split0Table4 = split0Table5 := by rfl

private theorem split0Stage5 : countTable [0, 0, 0, 0, 0] 0 = split0Table5 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0] 0) = split0Table5
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage4) split0Transition5

private def split0Table6 : List Nat :=
  [1]

private theorem split0Transition6 :
    extendTable 0 0 split0Table5 = split0Table6 := by rfl

private theorem split0Stage6 : countTable [0, 0, 0, 0, 0, 0] 0 = split0Table6 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0] 0) = split0Table6
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage5) split0Transition6

private def split0Table7 : List Nat :=
  [1]

private theorem split0Transition7 :
    extendTable 0 0 split0Table6 = split0Table7 := by rfl

private theorem split0Stage7 : countTable [0, 0, 0, 0, 0, 0, 0] 0 = split0Table7 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0] 0) = split0Table7
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage6) split0Transition7

private def split0Table8 : List Nat :=
  [1]

private theorem split0Transition8 :
    extendTable 0 0 split0Table7 = split0Table8 := by rfl

private theorem split0Stage8 : countTable [0, 0, 0, 0, 0, 0, 0, 0] 0 = split0Table8 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0] 0) = split0Table8
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage7) split0Transition8

private def split0Table9 : List Nat :=
  [1]

private theorem split0Transition9 :
    extendTable 0 0 split0Table8 = split0Table9 := by rfl

private theorem split0Stage9 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = split0Table9 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0] 0) = split0Table9
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage8) split0Transition9

private def split0Table10 : List Nat :=
  [1]

private theorem split0Transition10 :
    extendTable 0 0 split0Table9 = split0Table10 := by rfl

private theorem split0Stage10 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = split0Table10 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0, 0] 0) = split0Table10
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage9) split0Transition10

private def split0Table11 : List Nat :=
  [1]

private theorem split0Transition11 :
    extendTable 0 0 split0Table10 = split0Table11 := by rfl

private theorem split0Stage11 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = split0Table11 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0) = split0Table11
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage10) split0Transition11

private def split0Table12 : List Nat :=
  [1]

private theorem split0Transition12 :
    extendTable 0 0 split0Table11 = split0Table12 := by rfl

private theorem split0Stage12 : countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 = split0Table12 := by
  change extendTable 0 0 (countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0) = split0Table12
  exact Eq.trans (congrArg (extendTable 0 0) split0Stage11) split0Transition12

private theorem split0Exact : splitByCompositions 0 = splitLattice 0 := by
  change Int.ofNat ((countTable [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0).getD 0 0) = _
  calc
    _ = 1 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 0 0) split0Stage12) rfl)
    _ = _ := by decide

/-! Dilation 1, split slice. -/

private def split1Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0]

private theorem split1Stage0 : countTable [] 6 = split1Table0 := by rfl

private def split1Table1 : List Nat :=
  [1, 1, 0, 0, 0, 0, 0]

private theorem split1Transition1 :
    extendTable 6 1 split1Table0 = split1Table1 := by rfl

private theorem split1Stage1 : countTable [1] 6 = split1Table1 := by
  change extendTable 6 1 (countTable [] 6) = split1Table1
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage0) split1Transition1

private def split1Table2 : List Nat :=
  [1, 2, 1, 0, 0, 0, 0]

private theorem split1Transition2 :
    extendTable 6 1 split1Table1 = split1Table2 := by rfl

private theorem split1Stage2 : countTable [1, 1] 6 = split1Table2 := by
  change extendTable 6 1 (countTable [1] 6) = split1Table2
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage1) split1Transition2

private def split1Table3 : List Nat :=
  [1, 3, 3, 1, 0, 0, 0]

private theorem split1Transition3 :
    extendTable 6 1 split1Table2 = split1Table3 := by rfl

private theorem split1Stage3 : countTable [1, 1, 1] 6 = split1Table3 := by
  change extendTable 6 1 (countTable [1, 1] 6) = split1Table3
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage2) split1Transition3

private def split1Table4 : List Nat :=
  [1, 4, 6, 4, 1, 0, 0]

private theorem split1Transition4 :
    extendTable 6 1 split1Table3 = split1Table4 := by rfl

private theorem split1Stage4 : countTable [1, 1, 1, 1] 6 = split1Table4 := by
  change extendTable 6 1 (countTable [1, 1, 1] 6) = split1Table4
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage3) split1Transition4

private def split1Table5 : List Nat :=
  [1, 5, 10, 10, 5, 1, 0]

private theorem split1Transition5 :
    extendTable 6 1 split1Table4 = split1Table5 := by rfl

private theorem split1Stage5 : countTable [1, 1, 1, 1, 1] 6 = split1Table5 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1] 6) = split1Table5
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage4) split1Transition5

private def split1Table6 : List Nat :=
  [1, 6, 15, 20, 15, 6, 1]

private theorem split1Transition6 :
    extendTable 6 1 split1Table5 = split1Table6 := by rfl

private theorem split1Stage6 : countTable [1, 1, 1, 1, 1, 1] 6 = split1Table6 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1] 6) = split1Table6
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage5) split1Transition6

private def split1Table7 : List Nat :=
  [1, 7, 21, 35, 35, 21, 7]

private theorem split1Transition7 :
    extendTable 6 1 split1Table6 = split1Table7 := by rfl

private theorem split1Stage7 : countTable [1, 1, 1, 1, 1, 1, 1] 6 = split1Table7 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1] 6) = split1Table7
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage6) split1Transition7

private def split1Table8 : List Nat :=
  [1, 8, 28, 56, 70, 56, 28]

private theorem split1Transition8 :
    extendTable 6 1 split1Table7 = split1Table8 := by rfl

private theorem split1Stage8 : countTable [1, 1, 1, 1, 1, 1, 1, 1] 6 = split1Table8 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1] 6) = split1Table8
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage7) split1Transition8

private def split1Table9 : List Nat :=
  [1, 9, 36, 84, 126, 126, 84]

private theorem split1Transition9 :
    extendTable 6 1 split1Table8 = split1Table9 := by rfl

private theorem split1Stage9 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1] 6 = split1Table9 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1] 6) = split1Table9
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage8) split1Transition9

private def split1Table10 : List Nat :=
  [1, 10, 45, 120, 210, 252, 210]

private theorem split1Transition10 :
    extendTable 6 1 split1Table9 = split1Table10 := by rfl

private theorem split1Stage10 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6 = split1Table10 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1, 1] 6) = split1Table10
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage9) split1Transition10

private def split1Table11 : List Nat :=
  [1, 11, 55, 165, 330, 462, 462]

private theorem split1Transition11 :
    extendTable 6 1 split1Table10 = split1Table11 := by rfl

private theorem split1Stage11 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6 = split1Table11 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6) = split1Table11
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage10) split1Transition11

private def split1Table12 : List Nat :=
  [1, 12, 66, 220, 495, 792, 924]

private theorem split1Transition12 :
    extendTable 6 1 split1Table11 = split1Table12 := by rfl

private theorem split1Stage12 : countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6 = split1Table12 := by
  change extendTable 6 1 (countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6) = split1Table12
  exact Eq.trans (congrArg (extendTable 6 1) split1Stage11) split1Transition12

private theorem split1Exact : splitByCompositions 1 = splitLattice 1 := by
  change Int.ofNat ((countTable [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 6).getD 6 0) = _
  calc
    _ = 924 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 6 0) split1Stage12) rfl)
    _ = _ := by decide

/-! Dilation 2, split slice. -/

private def split2Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split2Stage0 : countTable [] 12 = split2Table0 := by rfl

private def split2Table1 : List Nat :=
  [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split2Transition1 :
    extendTable 12 2 split2Table0 = split2Table1 := by rfl

private theorem split2Stage1 : countTable [2] 12 = split2Table1 := by
  change extendTable 12 2 (countTable [] 12) = split2Table1
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage0) split2Transition1

private def split2Table2 : List Nat :=
  [1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split2Transition2 :
    extendTable 12 2 split2Table1 = split2Table2 := by rfl

private theorem split2Stage2 : countTable [2, 2] 12 = split2Table2 := by
  change extendTable 12 2 (countTable [2] 12) = split2Table2
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage1) split2Transition2

private def split2Table3 : List Nat :=
  [1, 3, 6, 7, 6, 3, 1, 0, 0, 0, 0, 0, 0]

private theorem split2Transition3 :
    extendTable 12 2 split2Table2 = split2Table3 := by rfl

private theorem split2Stage3 : countTable [2, 2, 2] 12 = split2Table3 := by
  change extendTable 12 2 (countTable [2, 2] 12) = split2Table3
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage2) split2Transition3

private def split2Table4 : List Nat :=
  [1, 4, 10, 16, 19, 16, 10, 4, 1, 0, 0, 0, 0]

private theorem split2Transition4 :
    extendTable 12 2 split2Table3 = split2Table4 := by rfl

private theorem split2Stage4 : countTable [2, 2, 2, 2] 12 = split2Table4 := by
  change extendTable 12 2 (countTable [2, 2, 2] 12) = split2Table4
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage3) split2Transition4

private def split2Table5 : List Nat :=
  [1, 5, 15, 30, 45, 51, 45, 30, 15, 5, 1, 0, 0]

private theorem split2Transition5 :
    extendTable 12 2 split2Table4 = split2Table5 := by rfl

private theorem split2Stage5 : countTable [2, 2, 2, 2, 2] 12 = split2Table5 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2] 12) = split2Table5
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage4) split2Transition5

private def split2Table6 : List Nat :=
  [1, 6, 21, 50, 90, 126, 141, 126, 90, 50, 21, 6, 1]

private theorem split2Transition6 :
    extendTable 12 2 split2Table5 = split2Table6 := by rfl

private theorem split2Stage6 : countTable [2, 2, 2, 2, 2, 2] 12 = split2Table6 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2] 12) = split2Table6
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage5) split2Transition6

private def split2Table7 : List Nat :=
  [1, 7, 28, 77, 161, 266, 357, 393, 357, 266, 161, 77, 28]

private theorem split2Transition7 :
    extendTable 12 2 split2Table6 = split2Table7 := by rfl

private theorem split2Stage7 : countTable [2, 2, 2, 2, 2, 2, 2] 12 = split2Table7 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2] 12) = split2Table7
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage6) split2Transition7

private def split2Table8 : List Nat :=
  [1, 8, 36, 112, 266, 504, 784, 1016, 1107, 1016, 784, 504, 266]

private theorem split2Transition8 :
    extendTable 12 2 split2Table7 = split2Table8 := by rfl

private theorem split2Stage8 : countTable [2, 2, 2, 2, 2, 2, 2, 2] 12 = split2Table8 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2] 12) = split2Table8
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage7) split2Transition8

private def split2Table9 : List Nat :=
  [1, 9, 45, 156, 414, 882, 1554, 2304, 2907, 3139, 2907, 2304, 1554]

private theorem split2Transition9 :
    extendTable 12 2 split2Table8 = split2Table9 := by rfl

private theorem split2Stage9 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2] 12 = split2Table9 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2] 12) = split2Table9
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage8) split2Transition9

private def split2Table10 : List Nat :=
  [1, 10, 55, 210, 615, 1452, 2850, 4740, 6765, 8350, 8953, 8350, 6765]

private theorem split2Transition10 :
    extendTable 12 2 split2Table9 = split2Table10 := by rfl

private theorem split2Stage10 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12 = split2Table10 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2, 2] 12) = split2Table10
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage9) split2Transition10

private def split2Table11 : List Nat :=
  [1, 11, 66, 275, 880, 2277, 4917, 9042, 14355, 19855, 24068, 25653, 24068]

private theorem split2Transition11 :
    extendTable 12 2 split2Table10 = split2Table11 := by rfl

private theorem split2Stage11 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12 = split2Table11 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12) = split2Table11
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage10) split2Transition11

private def split2Table12 : List Nat :=
  [1, 12, 78, 352, 1221, 3432, 8074, 16236, 28314, 43252, 58278, 69576, 73789]

private theorem split2Transition12 :
    extendTable 12 2 split2Table11 = split2Table12 := by rfl

private theorem split2Stage12 : countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12 = split2Table12 := by
  change extendTable 12 2 (countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12) = split2Table12
  exact Eq.trans (congrArg (extendTable 12 2) split2Stage11) split2Transition12

private theorem split2Exact : splitByCompositions 2 = splitLattice 2 := by
  change Int.ofNat ((countTable [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] 12).getD 12 0) = _
  calc
    _ = 73789 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 12 0) split2Stage12) rfl)
    _ = _ := by decide

/-! Dilation 3, split slice. -/

private def split3Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split3Stage0 : countTable [] 18 = split3Table0 := by rfl

private def split3Table1 : List Nat :=
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split3Transition1 :
    extendTable 18 3 split3Table0 = split3Table1 := by rfl

private theorem split3Stage1 : countTable [3] 18 = split3Table1 := by
  change extendTable 18 3 (countTable [] 18) = split3Table1
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage0) split3Transition1

private def split3Table2 : List Nat :=
  [1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split3Transition2 :
    extendTable 18 3 split3Table1 = split3Table2 := by rfl

private theorem split3Stage2 : countTable [3, 3] 18 = split3Table2 := by
  change extendTable 18 3 (countTable [3] 18) = split3Table2
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage1) split3Transition2

private def split3Table3 : List Nat :=
  [1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split3Transition3 :
    extendTable 18 3 split3Table2 = split3Table3 := by rfl

private theorem split3Stage3 : countTable [3, 3, 3] 18 = split3Table3 := by
  change extendTable 18 3 (countTable [3, 3] 18) = split3Table3
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage2) split3Transition3

private def split3Table4 : List Nat :=
  [1, 4, 10, 20, 31, 40, 44, 40, 31, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0]

private theorem split3Transition4 :
    extendTable 18 3 split3Table3 = split3Table4 := by rfl

private theorem split3Stage4 : countTable [3, 3, 3, 3] 18 = split3Table4 := by
  change extendTable 18 3 (countTable [3, 3, 3] 18) = split3Table4
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage3) split3Transition4

private def split3Table5 : List Nat :=
  [1, 5, 15, 35, 65, 101, 135, 155, 155, 135, 101, 65, 35, 15, 5, 1, 0, 0, 0]

private theorem split3Transition5 :
    extendTable 18 3 split3Table4 = split3Table5 := by rfl

private theorem split3Stage5 : countTable [3, 3, 3, 3, 3] 18 = split3Table5 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3] 18) = split3Table5
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage4) split3Transition5

private def split3Table6 : List Nat :=
  [1, 6, 21, 56, 120, 216, 336, 456, 546, 580, 546, 456, 336, 216, 120, 56, 21, 6, 1]

private theorem split3Transition6 :
    extendTable 18 3 split3Table5 = split3Table6 := by rfl

private theorem split3Stage6 : countTable [3, 3, 3, 3, 3, 3] 18 = split3Table6 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3] 18) = split3Table6
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage5) split3Transition6

private def split3Table7 : List Nat :=
  [1, 7, 28, 84, 203, 413, 728, 1128, 1554, 1918, 2128, 2128, 1918, 1554, 1128, 728, 413, 203, 84]

private theorem split3Transition7 :
    extendTable 18 3 split3Table6 = split3Table7 := by rfl

private theorem split3Stage7 : countTable [3, 3, 3, 3, 3, 3, 3] 18 = split3Table7 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3] 18) = split3Table7
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage6) split3Transition7

private def split3Table8 : List Nat :=
  [1, 8, 36, 120, 322, 728, 1428, 2472, 3823, 5328, 6728, 7728, 8092, 7728, 6728, 5328, 3823, 2472,
   1428]

private theorem split3Transition8 :
    extendTable 18 3 split3Table7 = split3Table8 := by rfl

private theorem split3Stage8 : countTable [3, 3, 3, 3, 3, 3, 3, 3] 18 = split3Table8 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3] 18) = split3Table8
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage7) split3Transition8

private def split3Table9 : List Nat :=
  [1, 9, 45, 165, 486, 1206, 2598, 4950, 8451, 13051, 18351, 23607, 27876, 30276, 30276, 27876,
   23607, 18351, 13051]

private theorem split3Transition9 :
    extendTable 18 3 split3Table8 = split3Table9 := by rfl

private theorem split3Stage9 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3] 18 = split3Table9 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3] 18) = split3Table9
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage8) split3Transition9

private def split3Table10 : List Nat :=
  [1, 10, 55, 220, 705, 1902, 4455, 9240, 17205, 29050, 44803, 63460, 82885, 100110, 112035, 116304,
   112035, 100110, 82885]

private theorem split3Transition10 :
    extendTable 18 3 split3Table9 = split3Table10 := by rfl

private theorem split3Stage10 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18 = split3Table10 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3, 3] 18) = split3Table10
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage9) split3Transition10

private def split3Table11 : List Nat :=
  [1, 11, 66, 286, 990, 2882, 7282, 16302, 32802, 59950, 100298, 154518, 220198, 291258, 358490,
   411334, 440484, 440484, 411334]

private theorem split3Transition11 :
    extendTable 18 3 split3Table10 = split3Table11 := by rfl

private theorem split3Stage11 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18 = split3Table11 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18) = split3Table11
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage10) split3Transition11

private def split3Table12 : List Nat :=
  [1, 12, 78, 364, 1353, 4224, 11440, 27456, 59268, 116336, 209352, 347568, 534964, 766272, 1024464,
   1281280, 1501566, 1650792, 1703636]

private theorem split3Transition12 :
    extendTable 18 3 split3Table11 = split3Table12 := by rfl

private theorem split3Stage12 : countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18 = split3Table12 := by
  change extendTable 18 3 (countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18) = split3Table12
  exact Eq.trans (congrArg (extendTable 18 3) split3Stage11) split3Transition12

private theorem split3Exact : splitByCompositions 3 = splitLattice 3 := by
  change Int.ofNat ((countTable [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] 18).getD 18 0) = _
  calc
    _ = 1703636 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 18 0) split3Stage12) rfl)
    _ = _ := by decide

/-! Dilation 4, split slice. -/

private def split4Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split4Stage0 : countTable [] 24 = split4Table0 := by rfl

private def split4Table1 : List Nat :=
  [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split4Transition1 :
    extendTable 24 4 split4Table0 = split4Table1 := by rfl

private theorem split4Stage1 : countTable [4] 24 = split4Table1 := by
  change extendTable 24 4 (countTable [] 24) = split4Table1
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage0) split4Transition1

private def split4Table2 : List Nat :=
  [1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split4Transition2 :
    extendTable 24 4 split4Table1 = split4Table2 := by rfl

private theorem split4Stage2 : countTable [4, 4] 24 = split4Table2 := by
  change extendTable 24 4 (countTable [4] 24) = split4Table2
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage1) split4Transition2

private def split4Table3 : List Nat :=
  [1, 3, 6, 10, 15, 18, 19, 18, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split4Transition3 :
    extendTable 24 4 split4Table2 = split4Table3 := by rfl

private theorem split4Stage3 : countTable [4, 4, 4] 24 = split4Table3 := by
  change extendTable 24 4 (countTable [4, 4] 24) = split4Table3
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage2) split4Transition3

private def split4Table4 : List Nat :=
  [1, 4, 10, 20, 35, 52, 68, 80, 85, 80, 68, 52, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split4Transition4 :
    extendTable 24 4 split4Table3 = split4Table4 := by rfl

private theorem split4Stage4 : countTable [4, 4, 4, 4] 24 = split4Table4 := by
  change extendTable 24 4 (countTable [4, 4, 4] 24) = split4Table4
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage3) split4Transition4

private def split4Table5 : List Nat :=
  [1, 5, 15, 35, 70, 121, 185, 255, 320, 365, 381, 365, 320, 255, 185, 121, 70, 35, 15, 5, 1, 0, 0,
   0, 0]

private theorem split4Transition5 :
    extendTable 24 4 split4Table4 = split4Table5 := by rfl

private theorem split4Stage5 : countTable [4, 4, 4, 4, 4] 24 = split4Table5 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4] 24) = split4Table5
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage4) split4Transition5

private def split4Table6 : List Nat :=
  [1, 6, 21, 56, 126, 246, 426, 666, 951, 1246, 1506, 1686, 1751, 1686, 1506, 1246, 951, 666, 426,
   246, 126, 56, 21, 6, 1]

private theorem split4Transition6 :
    extendTable 24 4 split4Table5 = split4Table6 := by rfl

private theorem split4Stage6 : countTable [4, 4, 4, 4, 4, 4] 24 = split4Table6 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4] 24) = split4Table6
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage5) split4Transition6

private def split4Table7 : List Nat :=
  [1, 7, 28, 84, 210, 455, 875, 1520, 2415, 3535, 4795, 6055, 7140, 7875, 8135, 7875, 7140, 6055,
   4795, 3535, 2415, 1520, 875, 455, 210]

private theorem split4Transition7 :
    extendTable 24 4 split4Table6 = split4Table7 := by rfl

private theorem split4Stage7 : countTable [4, 4, 4, 4, 4, 4, 4] 24 = split4Table7 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4] 24) = split4Table7
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage6) split4Transition7

private def split4Table8 : List Nat :=
  [1, 8, 36, 120, 330, 784, 1652, 3144, 5475, 8800, 13140, 18320, 23940, 29400, 34000, 37080, 38165,
   37080, 34000, 29400, 23940, 18320, 13140, 8800, 5475]

private theorem split4Transition8 :
    extendTable 24 4 split4Table7 = split4Table8 := by rfl

private theorem split4Stage8 : countTable [4, 4, 4, 4, 4, 4, 4, 4] 24 = split4Table8 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4] 24) = split4Table8
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage7) split4Transition8

private def split4Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1278, 2922, 6030, 11385, 19855, 32211, 48879, 69675, 93600, 118800, 142740,
   162585, 175725, 180325, 175725, 162585, 142740, 118800, 93600, 69675]

private theorem split4Transition9 :
    extendTable 24 4 split4Table8 = split4Table9 := by rfl

private theorem split4Stage9 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4] 24 = split4Table9 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4] 24) = split4Table9
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage8) split4Transition9

private def split4Table10 : List Nat :=
  [1, 10, 55, 220, 715, 1992, 4905, 10890, 22110, 41470, 72403, 118360, 182005, 264220, 363165,
   473694, 587400, 693450, 780175, 837100, 856945, 837100, 780175, 693450, 587400]

private theorem split4Transition10 :
    extendTable 24 4 split4Table9 = split4Table10 := by rfl

private theorem split4Stage10 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24 = split4Table10 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4, 4] 24) = split4Table10
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage9) split4Transition10

private def split4Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 2992, 7887, 18722, 40612, 81367, 151778, 265233, 436348, 678458, 1000153,
   1401444, 1870484, 2381929, 2897884, 3371819, 3755070, 4004770, 4091495, 4004770, 3755070]

private theorem split4Transition11 :
    extendTable 24 4 split4Table10 = split4Table11 := by rfl

private theorem split4Stage11 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24 = split4Table11 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24) = split4Table11
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage10) split4Transition11

private def split4Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4356, 12232, 30888, 71214, 151580, 300366, 557712, 975338, 1613184,
   2531970, 3781636, 5386887, 7332468, 9551894, 11923560, 14277186, 16411472, 18121038, 19227924,
   19611175]

private theorem split4Transition12 :
    extendTable 24 4 split4Table11 = split4Table12 := by rfl

private theorem split4Stage12 : countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24 = split4Table12 := by
  change extendTable 24 4 (countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24) = split4Table12
  exact Eq.trans (congrArg (extendTable 24 4) split4Stage11) split4Transition12

private theorem split4Exact : splitByCompositions 4 = splitLattice 4 := by
  change Int.ofNat ((countTable [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] 24).getD 24 0) = _
  calc
    _ = 19611175 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 24 0) split4Stage12) rfl)
    _ = _ := by decide

/-! Dilation 5, split slice. -/

private def split5Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split5Stage0 : countTable [] 30 = split5Table0 := by rfl

private def split5Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split5Transition1 :
    extendTable 30 5 split5Table0 = split5Table1 := by rfl

private theorem split5Stage1 : countTable [5] 30 = split5Table1 := by
  change extendTable 30 5 (countTable [] 30) = split5Table1
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage0) split5Transition1

private def split5Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split5Transition2 :
    extendTable 30 5 split5Table1 = split5Table2 := by rfl

private theorem split5Stage2 : countTable [5, 5] 30 = split5Table2 := by
  change extendTable 30 5 (countTable [5] 30) = split5Table2
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage1) split5Transition2

private def split5Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 25, 27, 27, 25, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0]

private theorem split5Transition3 :
    extendTable 30 5 split5Table2 = split5Table3 := by rfl

private theorem split5Stage3 : countTable [5, 5, 5] 30 = split5Table3 := by
  change extendTable 30 5 (countTable [5, 5] 30) = split5Table3
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage2) split5Transition3

private def split5Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 80, 104, 125, 140, 146, 140, 125, 104, 80, 56, 35, 20, 10, 4, 1, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0]

private theorem split5Transition4 :
    extendTable 30 5 split5Table3 = split5Table4 := by rfl

private theorem split5Stage4 : countTable [5, 5, 5, 5] 30 = split5Table4 := by
  change extendTable 30 5 (countTable [5, 5, 5] 30) = split5Table4
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage3) split5Transition4

private def split5Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 205, 305, 420, 540, 651, 735, 780, 780, 735, 651, 540, 420, 305, 205, 126,
   70, 35, 15, 5, 1, 0, 0, 0, 0, 0]

private theorem split5Transition5 :
    extendTable 30 5 split5Table4 = split5Table5 := by rfl

private theorem split5Stage5 : countTable [5, 5, 5, 5, 5] 30 = split5Table5 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5] 30) = split5Table5
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage4) split5Transition5

private def split5Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 456, 756, 1161, 1666, 2247, 2856, 3431, 3906, 4221, 4332, 4221, 3906,
   3431, 2856, 2247, 1666, 1161, 756, 456, 252, 126, 56, 21, 6, 1]

private theorem split5Transition6 :
    extendTable 30 5 split5Table5 = split5Table6 := by rfl

private theorem split5Stage6 : countTable [5, 5, 5, 5, 5, 5] 30 = split5Table6 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5] 30) = split5Table6
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage5) split5Transition6

private def split5Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 917, 1667, 2807, 4417, 6538, 9142, 12117, 15267, 18327, 20993, 22967,
   24017, 24017, 22967, 20993, 18327, 15267, 12117, 9142, 6538, 4417, 2807, 1667, 917, 462]

private theorem split5Transition7 :
    extendTable 30 5 split5Table6 = split5Table7 := by rfl

private theorem split5Stage7 : countTable [5, 5, 5, 5, 5, 5, 5] 30 = split5Table7 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5] 30) = split5Table7
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage6) split5Transition7

private def split5Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1708, 3368, 6147, 10480, 16808, 25488, 36688, 50288, 65808, 82384,
   98813, 113688, 125588, 133288, 135954, 133288, 125588, 113688, 98813, 82384, 65808, 50288, 36688,
   25488, 16808]

private theorem split5Transition8 :
    extendTable 30 5 split5Table7 = split5Table8 := by rfl

private theorem split5Stage8 : countTable [5, 5, 5, 5, 5, 5, 5, 5] 30 = split5Table8 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5] 30) = split5Table8
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage7) split5Transition8

private def split5Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 2994, 6354, 12465, 22825, 39303, 63999, 98979, 145899, 205560, 277464,
   359469, 447669, 536569, 619569, 689715, 740619, 767394, 767394, 740619, 689715, 619569, 536569,
   447669, 359469, 277464]

private theorem split5Transition9 :
    extendTable 30 5 split5Table8 = split5Table9 := by rfl

private theorem split5Stage9 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5] 30 = split5Table9 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5] 30) = split5Table9
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage8) split5Transition9

private def split5Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 4995, 11340, 23760, 46420, 85228, 147940, 243925, 383470, 576565,
   831204, 1151370, 1535040, 1972630, 2446300, 2930455, 3393610, 3801535, 4121260, 4325310, 4395456,
   4325310, 4121260, 3801535, 3393610, 2930455]

private theorem split5Transition10 :
    extendTable 30 5 split5Table9 = split5Table10 := by rfl

private theorem split5Stage10 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30 = split5Table10 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5, 5] 30) = split5Table10
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage9) split5Transition10

private def split5Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 7997, 19327, 43032, 89232, 173745, 319683, 558613, 930743, 1483548,
   2268332, 3334474, 4721574, 6450279, 8513109, 10866999, 13429405, 16079570, 18665790, 21018470,
   22967626, 24362481, 25090131, 25090131, 24362481, 22967626]

private theorem split5Transition11 :
    extendTable 30 5 split5Table10 = split5Table11 := by rfl

private theorem split5Stage11 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30 = split5Table11 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30) = split5Table11
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage10) split5Transition11

private def split5Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12364, 31680, 74646, 163592, 336336, 653016, 1203632, 2115048,
   3555564, 5734664, 8895393, 13297284, 19188950, 26771316, 36154767, 47315840, 60060936, 74005152,
   88573343, 103027860, 116523342, 128184068, 137194629, 142891320, 144840476]

private theorem split5Transition12 :
    extendTable 30 5 split5Table11 = split5Table12 := by rfl

private theorem split5Stage12 : countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30 = split5Table12 := by
  change extendTable 30 5 (countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30) = split5Table12
  exact Eq.trans (congrArg (extendTable 30 5) split5Stage11) split5Transition12

private theorem split5Exact : splitByCompositions 5 = splitLattice 5 := by
  change Int.ofNat ((countTable [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] 30).getD 30 0) = _
  calc
    _ = 144840476 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 30 0) split5Stage12) rfl)
    _ = _ := by decide

/-! Dilation 6, split slice. -/

private def split6Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem split6Stage0 : countTable [] 36 = split6Table0 := by rfl

private def split6Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem split6Transition1 :
    extendTable 36 6 split6Table0 = split6Table1 := by rfl

private theorem split6Stage1 : countTable [6] 36 = split6Table1 := by
  change extendTable 36 6 (countTable [] 36) = split6Table1
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage0) split6Transition1

private def split6Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem split6Transition2 :
    extendTable 36 6 split6Table1 = split6Table2 := by rfl

private theorem split6Stage2 : countTable [6, 6] 36 = split6Table2 := by
  change extendTable 36 6 (countTable [6] 36) = split6Table2
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage1) split6Transition2

private def split6Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 33, 36, 37, 36, 33, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split6Transition3 :
    extendTable 36 6 split6Table2 = split6Table3 := by rfl

private theorem split6Stage3 : countTable [6, 6, 6] 36 = split6Table3 := by
  change extendTable 36 6 (countTable [6, 6] 36) = split6Table3
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage2) split6Transition3

private def split6Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 116, 149, 180, 206, 224, 231, 224, 206, 180, 149, 116, 84, 56, 35, 20,
   10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split6Transition4 :
    extendTable 36 6 split6Table3 = split6Table4 := by rfl

private theorem split6Stage4 : countTable [6, 6, 6, 6] 36 = split6Table4 := by
  change extendTable 36 6 (countTable [6, 6, 6] 36) = split6Table4
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage3) split6Transition4

private def split6Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 325, 470, 640, 826, 1015, 1190, 1330, 1420, 1451, 1420, 1330, 1190,
   1015, 826, 640, 470, 325, 210, 126, 70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0]

private theorem split6Transition5 :
    extendTable 36 6 split6Table4 = split6Table5 := by rfl

private theorem split6Stage5 : countTable [6, 6, 6, 6, 6] 36 = split6Table5 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6] 36) = split6Table5
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage4) split6Transition5

private def split6Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 786, 1251, 1876, 2667, 3612, 4676, 5796, 6891, 7872, 8652, 9156,
   9331, 9156, 8652, 7872, 6891, 5796, 4676, 3612, 2667, 1876, 1251, 786, 462, 252, 126, 56, 21, 6,
   1]

private theorem split6Transition6 :
    extendTable 36 6 split6Table5 = split6Table6 := by rfl

private theorem split6Stage6 : countTable [6, 6, 6, 6, 6, 6] 36 = split6Table6 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6] 36) = split6Table6
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage5) split6Transition6

private def split6Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1709, 2954, 4809, 7420, 10906, 15330, 20664, 26769, 33390, 40166,
   46655, 52374, 56854, 59710, 60691, 59710, 56854, 52374, 46655, 40166, 33390, 26769, 20664, 15330,
   10906, 7420, 4809, 2954, 1709, 924]

private theorem split6Transition7 :
    extendTable 36 6 split6Table6 = split6Table7 := by rfl

private theorem split6Stage7 : countTable [6, 6, 6, 6, 6, 6, 6] 36 = split6Table7 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6] 36) = split6Table7
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage6) split6Transition7

private def split6Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3424, 6371, 11152, 18488, 29184, 44052, 63792, 88852, 119288,
   154645, 193880, 235348, 276872, 315918, 349840, 376160, 392848, 398567, 392848, 376160, 349840,
   315918, 276872, 235348, 193880, 154645, 119288, 88852, 63792, 44052]

private theorem split6Transition8 :
    extendTable 36 6 split6Table7 = split6Table8 := by rfl

private theorem split6Stage8 : countTable [6, 6, 6, 6, 6, 6, 6, 6] 36 = split6Table8 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6] 36) = split6Table8
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage7) split6Transition8

private def split6Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6426, 12789, 23905, 42273, 71127, 114387, 176463, 261891, 374808,
   518301, 693693, 899857, 1132677, 1384803, 1645791, 1902663, 2140866, 2345553, 2503053, 2602341,
   2636263, 2602341, 2503053, 2345553, 2140866, 1902663, 1645791, 1384803, 1132677, 899857]

private theorem split6Transition9 :
    extendTable 36 6 split6Table8 = split6Table9 := by rfl

private theorem split6Stage9 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6] 36 = split6Table9 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6] 36) = split6Table9
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage8) split6Transition9

private def split6Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11430, 24210, 48070, 90178, 160810, 273910, 447370, 702835,
   1064854, 1559250, 2210670, 3039400, 4057690, 5266030, 6649930, 8177785, 9800350, 11452210,
   13055406, 14525070, 15776530, 16733080, 17333470, 17538157, 17333470, 16733080, 15776530,
   14525070, 13055406, 11452210]

private theorem split6Transition10 :
    extendTable 36 6 split6Table9 = split6Table10 := by rfl

private theorem split6Stage10 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36 = split6Table10 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6, 6] 36) = split6Table10
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage9) split6Transition10

private def split6Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19437, 43637, 91652, 181610, 341705, 613613, 1055978, 1747383,
   2788027, 4299207, 6419699, 9298289, 13082069, 17900729, 23847824, 30960755, 39201855, 48443395,
   58459401, 68926781, 79437281, 89520431, 98676116, 106413923, 112295183, 115972857, 117224317,
   115972857, 112295183, 106413923]

private theorem split6Transition11 :
    extendTable 36 6 split6Table10 = split6Table11 := by rfl

private theorem split6Stage11 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36 = split6Table11 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36) = split6Table11
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage10) split6Transition11

private def split6Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31812, 75438, 167024, 348348, 689052, 1299662, 2347632,
   4075578, 6819968, 11027523, 17265612, 26222196, 38690652, 55535403, 77635844, 105808572,
   140711220, 182734916, 231896028, 287740740, 349277292, 414949899, 482665260, 549877328,
   613729116, 671242572, 719540108, 756075684, 778850436, 786588243]

private theorem split6Transition12 :
    extendTable 36 6 split6Table11 = split6Table12 := by rfl

private theorem split6Stage12 : countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36 = split6Table12 := by
  change extendTable 36 6 (countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36) = split6Table12
  exact Eq.trans (congrArg (extendTable 36 6) split6Stage11) split6Transition12

private theorem split6Exact : splitByCompositions 6 = splitLattice 6 := by
  change Int.ofNat ((countTable [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] 36).getD 36 0) = _
  calc
    _ = 786588243 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 36 0) split6Stage12) rfl)
    _ = _ := by decide

/-! Dilation 7, split slice. -/

private def split7Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split7Stage0 : countTable [] 42 = split7Table0 := by rfl

private def split7Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split7Transition1 :
    extendTable 42 7 split7Table0 = split7Table1 := by rfl

private theorem split7Stage1 : countTable [7] 42 = split7Table1 := by
  change extendTable 42 7 (countTable [] 42) = split7Table1
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage0) split7Transition1

private def split7Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split7Transition2 :
    extendTable 42 7 split7Table1 = split7Table2 := by rfl

private theorem split7Stage2 : countTable [7, 7] 42 = split7Table2 := by
  change extendTable 42 7 (countTable [7] 42) = split7Table2
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage1) split7Transition2

private def split7Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 42, 46, 48, 48, 46, 42, 36, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split7Transition3 :
    extendTable 42 7 split7Table2 = split7Table3 := by rfl

private theorem split7Stage3 : countTable [7, 7, 7] 42 = split7Table3 := by
  change extendTable 42 7 (countTable [7, 7] 42) = split7Table3
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage2) split7Transition3

private def split7Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 161, 204, 246, 284, 315, 336, 344, 336, 315, 284, 246, 204, 161,
   120, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split7Transition4 :
    extendTable 42 7 split7Table3 = split7Table4 := by rfl

private theorem split7Stage4 : countTable [7, 7, 7, 7] 42 = split7Table4 := by
  change extendTable 42 7 (countTable [7, 7, 7] 42) = split7Table4
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage3) split7Transition4

private def split7Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 490, 690, 926, 1190, 1470, 1750, 2010, 2226, 2380, 2460, 2460,
   2380, 2226, 2010, 1750, 1470, 1190, 926, 690, 490, 330, 210, 126, 70, 35, 15, 5, 1, 0, 0, 0, 0,
   0, 0, 0]

private theorem split7Transition5 :
    extendTable 42 7 split7Table4 = split7Table5 := by rfl

private theorem split7Stage5 : countTable [7, 7, 7, 7, 7] 42 = split7Table5 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7] 42) = split7Table5
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage4) split7Transition5

private def split7Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1281, 1966, 2877, 4032, 5432, 7056, 8856, 10752, 12642, 14412,
   15946, 17136, 17892, 18152, 17892, 17136, 15946, 14412, 12642, 10752, 8856, 7056, 5432, 4032,
   2877, 1966, 1281, 792, 462, 252, 126, 56, 21, 6, 1]

private theorem split7Transition6 :
    extendTable 42 7 split7Table5 = split7Table6 := by rfl

private theorem split7Stage6 : countTable [7, 7, 7, 7, 7, 7] 42 = split7Table6 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7] 42) = split7Table6
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage5) split7Transition6

private def split7Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 2996, 4956, 7812, 11788, 17094, 23898, 32292, 42252, 53613,
   66059, 79128, 92232, 104692, 115788, 124824, 131208, 134512, 134512, 131208, 124824, 115788,
   104692, 92232, 79128, 66059, 53613, 42252, 32292, 23898, 17094, 11788, 7812, 4956, 2996, 1716]

private theorem split7Transition7 :
    extendTable 42 7 split7Table6 = split7Table7 := by rfl

private theorem split7Stage7 : countTable [7, 7, 7, 7, 7, 7, 7] 42 = split7Table7 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7] 42) = split7Table7
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage6) split7Transition7

private def split7Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6427, 11376, 19160, 30864, 47748, 71184, 102552, 143088,
   193705, 254808, 326124, 406568, 494166, 586056, 678588, 767544, 848443, 916896, 968976, 1001568,
   1012664, 1001568, 968976, 916896, 848443, 767544, 678588, 586056, 494166, 406568, 326124, 254808,
   193705, 143088, 102552]

private theorem split7Transition8 :
    extendTable 42 7 split7Table7 = split7Table8 := by rfl

private theorem split7Stage8 : countTable [7, 7, 7, 7, 7, 7, 7, 7] 42 = split7Table8 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7] 42) = split7Table8
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage7) split7Transition8

private def split7Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12861, 24229, 43353, 74097, 121515, 191907, 292743, 432399,
   619677, 863109, 1170073, 1545777, 1992195, 2507067, 3083103, 3707559, 4362297, 5024385, 5667237,
   6262237, 6780735, 7196247, 7486635, 7635987, 7635987, 7486635, 7196247, 6780735, 6262237,
   5667237, 5024385, 4362297, 3707559, 3083103, 2507067]

private theorem split7Transition9 :
    extendTable 42 7 split7Table8 = split7Table9 := by rfl

private theorem split7Stage9 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7] 42 = split7Table9 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7] 42) = split7Table9
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage8) split7Transition9

private def split7Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24300, 48520, 91828, 165760, 286780, 477400, 767140,
   1193104, 1799920, 2638800, 3765520, 5237200, 7107880, 9423040, 12213400, 15488560, 19231180,
   23392456, 27889620, 32606080, 37394620, 42083800, 46487332, 50415760, 53689450, 56151700,
   57680710, 58199208, 57680710, 56151700, 53689450, 50415760, 46487332, 42083800, 37394620]

private theorem split7Transition10 :
    extendTable 42 7 split7Table9 = split7Table10 := by rfl

private theorem split7Stage10 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42 = split7Table10 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7, 7] 42) = split7Table10
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage9) split7Transition10

private def split7Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43747, 92257, 184030, 349570, 635635, 1111033, 1873168,
   3054832, 4830452, 7420732, 11094424, 16165864, 22986964, 31932604, 43378864, 57674320, 75105580,
   95859236, 119983336, 147352216, 177638956, 210299716, 244573648, 279500848, 313959118, 346718362,
   376509452, 402102580, 422388670, 436456570, 443658688, 443658688, 436456570, 422388670,
   402102580]

private theorem split7Transition11 :
    extendTable 42 7 split7Table10 = split7Table11 := by rfl

private theorem split7Stage11 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42 = split7Table11 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42) = split7Table11
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage10) split7Transition11

private def split7Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31824, 75570, 167816, 351780, 701064, 1335698, 2443728,
   4308888, 7344272, 12130977, 19459452, 30369846, 46186140, 68537469, 99359040, 140864736,
   195484224, 265759352, 354197856, 463086768, 594273120, 748925112, 927292224, 1128487008,
   1350313536, 1589167074, 1840026200, 2096552316, 2351302680, 2596052394, 2822209248, 3021294288,
   3185452128, 3307949580, 3383619888, 3409213016]

private theorem split7Transition12 :
    extendTable 42 7 split7Table11 = split7Table12 := by rfl

private theorem split7Stage12 : countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42 = split7Table12 := by
  change extendTable 42 7 (countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42) = split7Table12
  exact Eq.trans (congrArg (extendTable 42 7) split7Stage11) split7Transition12

private theorem split7Exact : splitByCompositions 7 = splitLattice 7 := by
  change Int.ofNat ((countTable [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] 42).getD 42 0) = _
  calc
    _ = 3409213016 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 42 0) split7Stage12) rfl)
    _ = _ := by decide

/-! Dilation 8, split slice. -/

private def split8Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split8Stage0 : countTable [] 48 = split8Table0 := by rfl

private def split8Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split8Transition1 :
    extendTable 48 8 split8Table0 = split8Table1 := by rfl

private theorem split8Stage1 : countTable [8] 48 = split8Table1 := by
  change extendTable 48 8 (countTable [] 48) = split8Table1
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage0) split8Transition1

private def split8Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split8Transition2 :
    extendTable 48 8 split8Table1 = split8Table2 := by rfl

private theorem split8Stage2 : countTable [8, 8] 48 = split8Table2 := by
  change extendTable 48 8 (countTable [8] 48) = split8Table2
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage1) split8Transition2

private def split8Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 52, 57, 60, 61, 60, 57, 52, 45, 36, 28, 21, 15, 10, 6, 3, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split8Transition3 :
    extendTable 48 8 split8Table2 = split8Table3 := by rfl

private theorem split8Stage3 : countTable [8, 8, 8] 48 = split8Table3 := by
  change extendTable 48 8 (countTable [8, 8] 48) = split8Table3
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage2) split8Transition3

private def split8Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 216, 270, 324, 375, 420, 456, 480, 489, 480, 456, 420, 375,
   324, 270, 216, 165, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0]

private theorem split8Transition4 :
    extendTable 48 8 split8Table3 = split8Table4 := by rfl

private theorem split8Stage4 : countTable [8, 8, 8, 8] 48 = split8Table4 := by
  change extendTable 48 8 (countTable [8, 8, 8] 48) = split8Table4
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage3) split8Transition4

private def split8Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 710, 976, 1290, 1645, 2030, 2430, 2826, 3195, 3510, 3750,
   3900, 3951, 3900, 3750, 3510, 3195, 2826, 2430, 2030, 1645, 1290, 976, 710, 495, 330, 210, 126,
   70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split8Transition5 :
    extendTable 48 8 split8Table4 = split8Table5 := by rfl

private theorem split8Stage5 : countTable [8, 8, 8, 8, 8] 48 = split8Table5 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8] 48) = split8Table5
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage4) split8Transition5

private def split8Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 1996, 2967, 4242, 5852, 7812, 10116, 12732, 15597, 18612,
   21652, 24576, 27237, 29492, 31212, 32292, 32661, 32292, 31212, 29492, 27237, 24576, 21652, 18612,
   15597, 12732, 10116, 7812, 5852, 4242, 2967, 1996, 1287, 792, 462, 252, 126, 56, 21, 6, 1]

private theorem split8Transition6 :
    extendTable 48 8 split8Table5 = split8Table6 := by rfl

private theorem split8Stage6 : countTable [8, 8, 8, 8, 8, 8] 48 = split8Table6 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8] 48) = split8Table6
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage5) split8Transition6

private def split8Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 4998, 7959, 12180, 17976, 25662, 35526, 47796, 62601,
   79926, 99582, 121191, 144186, 167826, 191226, 213402, 233331, 250026, 262626, 270466, 273127,
   270466, 262626, 250026, 233331, 213402, 191226, 167826, 144186, 121191, 99582, 79926, 62601,
   47796, 35526, 25662, 17976, 12180, 7959, 4998, 3003]

private theorem split8Transition7 :
    extendTable 48 8 split8Table6 = split8Table7 := by rfl

private theorem split8Stage7 : countTable [8, 8, 8, 8, 8, 8, 8] 48 = split8Table7 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8] 48) = split8Table7
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage6) split8Transition7

private def split8Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11432, 19384, 31536, 49428, 74880, 109944, 156816,
   217701, 294624, 389208, 502440, 634446, 784296, 949860, 1127736, 1313271, 1500696, 1683396,
   1854280, 2006216, 2132496, 2227296, 2286096, 2306025, 2286096, 2227296, 2132496, 2006216,
   1854280, 1683396, 1500696, 1313271, 1127736, 949860, 784296, 634446, 502440, 389208, 294624,
   217701]

private theorem split8Transition8 :
    extendTable 48 8 split8Table7 = split8Table8 := by rfl

private theorem split8Stage8 : countTable [8, 8, 8, 8, 8, 8, 8, 8] 48 = split8Table8 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8] 48) = split8Table8
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage7) split8Transition8

private def split8Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24301, 43677, 75177, 124485, 199035, 308187, 463287,
   677556, 965745, 1343521, 1826577, 2429487, 3164355, 4039335, 5057127, 6213582, 7496577, 8885349,
   10350421, 11854197, 13352247, 14795247, 16131483, 17309772, 18282597, 19009197, 19458297,
   19610233, 19458297, 19009197, 18282597, 17309772, 16131483, 14795247, 13352247, 11854197,
   10350421, 8885349, 7496577, 6213582]

private theorem split8Transition9 :
    extendTable 48 8 split8Table8 = split8Table9 := by rfl

private theorem split8Stage9 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8] 48 = split8Table9 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8] 48) = split8Table9
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage8) split8Transition9

private def split8Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48610, 92278, 167410, 291730, 490270, 797170,
   1257454, 1928575, 2881450, 4200670, 5983570, 8337880, 11377750, 15218050, 19966990, 25717285,
   32536306, 40455910, 49462810, 59490430, 70413190, 82044082, 94136230, 106388875, 118457890,
   129970510, 140543458, 149803270, 157407370, 163064320, 166551670, 167729959, 166551670,
   163064320, 157407370, 149803270, 140543458, 129970510, 118457890, 106388875]

private theorem split8Transition10 :
    extendTable 48 8 split8Table9 = split8Table10 := by rfl

private theorem split8Stage10 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48 = split8Table10 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8, 8] 48) = split8Table10
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage9) split8Transition10

private def split8Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92367, 184635, 351990, 643500, 1133055, 1928223,
   3180672, 5097807, 7954947, 12107007, 17998299, 26168769, 37254789, 51982569, 71152389, 95612220,
   126219951, 163794411, 209056551, 262563411, 324638721, 395305053, 474223233, 560645118,
   653385723, 750819927, 850907475, 951247935, 1049164875, 1141816005, 1226323593, 1299917322,
   1360080117, 1404686547, 1432123407, 1441383219, 1432123407, 1404686547, 1360080117, 1299917322]

private theorem split8Transition11 :
    extendTable 48 8 split8Table10 = split8Table11 := by rfl

private theorem split8Stage11 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48 = split8Table11 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48) = split8Table11
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage10) split8Transition11

private def split8Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31824, 75582, 167948, 352572, 704496, 1347710, 2479764,
   4404984, 7577648, 12656007, 20567196, 32581836, 50395500, 76212279, 112823568, 163673082,
   232897248, 325328796, 446450940, 602290404, 799239948, 1043805060, 1342275012, 1700325276,
   2122565940, 2612058669, 3169832172, 3794432148, 4481545212, 5223736596, 6010338060, 6827515344,
   7658533884, 8484227973, 9283662972, 10034963796, 10716267276, 11306743020, 11787618492,
   12143140164, 12361404276, 12434998005]

private theorem split8Transition12 :
    extendTable 48 8 split8Table11 = split8Table12 := by rfl

private theorem split8Stage12 : countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48 = split8Table12 := by
  change extendTable 48 8 (countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48) = split8Table12
  exact Eq.trans (congrArg (extendTable 48 8) split8Stage11) split8Transition12

private theorem split8Exact : splitByCompositions 8 = splitLattice 8 := by
  change Int.ofNat ((countTable [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8] 48).getD 48 0) = _
  calc
    _ = 12434998005 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 48 0) split8Stage12) rfl)
    _ = _ := by decide

/-! Dilation 9, split slice. -/

private def split9Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Stage0 : countTable [] 54 = split9Table0 := by rfl

private def split9Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Transition1 :
    extendTable 54 9 split9Table0 = split9Table1 := by rfl

private theorem split9Stage1 : countTable [9] 54 = split9Table1 := by
  change extendTable 54 9 (countTable [] 54) = split9Table1
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage0) split9Transition1

private def split9Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Transition2 :
    extendTable 54 9 split9Table1 = split9Table2 := by rfl

private theorem split9Stage2 : countTable [9, 9] 54 = split9Table2 := by
  change extendTable 54 9 (countTable [9] 54) = split9Table2
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage1) split9Transition2

private def split9Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 63, 69, 73, 75, 75, 73, 69, 63, 55, 45, 36, 28, 21, 15, 10,
   6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Transition3 :
    extendTable 54 9 split9Table2 = split9Table3 := by rfl

private theorem split9Stage3 : countTable [9, 9, 9] 54 = split9Table3 := by
  change extendTable 54 9 (countTable [9, 9] 54) = split9Table3
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage2) split9Transition3

private def split9Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 282, 348, 415, 480, 540, 592, 633, 660, 670, 660, 633,
   592, 540, 480, 415, 348, 282, 220, 165, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Transition4 :
    extendTable 54 9 split9Table3 = split9Table4 := by rfl

private theorem split9Stage4 : countTable [9, 9, 9, 9] 54 = split9Table4 := by
  change extendTable 54 9 (countTable [9, 9, 9] 54) = split9Table4
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage3) split9Transition4

private def split9Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 996, 1340, 1745, 2205, 2710, 3246, 3795, 4335, 4840,
   5280, 5631, 5875, 6000, 6000, 5875, 5631, 5280, 4840, 4335, 3795, 3246, 2710, 2205, 1745, 1340,
   996, 715, 495, 330, 210, 126, 70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split9Transition5 :
    extendTable 54 9 split9Table4 = split9Table5 := by rfl

private theorem split9Stage5 : countTable [9, 9, 9, 9, 9] 54 = split9Table5 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9] 54) = split9Table5
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage4) split9Transition5

private def split9Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 2002, 2997, 4332, 6062, 8232, 10872, 13992, 17577, 21582,
   25927, 30492, 35127, 39662, 43917, 47712, 50877, 53262, 54747, 55252, 54747, 53262, 50877, 47712,
   43917, 39662, 35127, 30492, 25927, 21582, 17577, 13992, 10872, 8232, 6062, 4332, 2997, 2002,
   1287, 792, 462, 252, 126, 56, 21, 6, 1]

private theorem split9Transition6 :
    extendTable 54 9 split9Table5 = split9Table6 := by rfl

private theorem split9Stage6 : countTable [9, 9, 9, 9, 9, 9] 54 = split9Table6 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9] 54) = split9Table6
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage5) split9Transition6

private def split9Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8001, 12327, 18368, 26544, 37290, 51030, 68145,
   88935, 113575, 142065, 174195, 209525, 247380, 286860, 326865, 366135, 403305, 436975, 465795,
   488565, 504315, 512365, 512365, 504315, 488565, 465795, 436975, 403305, 366135, 326865, 286860,
   247380, 209525, 174195, 142065, 113575, 88935, 68145, 51030, 37290, 26544, 18368, 12327, 8001,
   5005]

private theorem split9Transition7 :
    extendTable 54 9 split9Table6 = split9Table7 := by rfl

private theorem split9Stage7 : countTable [9, 9, 9, 9, 9, 9, 9] 54 = split9Table7 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9] 54) = split9Table7
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage6) split9Transition7

private def split9Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11440, 19440, 31760, 50100, 76560, 113640, 164208,
   231429, 318648, 429220, 566280, 732474, 929672, 1158684, 1419000, 1708575, 2023680, 2358840,
   2706880, 3059100, 3405600, 3735720, 4038560, 4303545, 4521000, 4682700, 4782360, 4816030,
   4782360, 4682700, 4521000, 4303545, 4038560, 3735720, 3405600, 3059100, 2706880, 2358840,
   2023680, 1708575, 1419000, 1158684, 929672, 732474, 566280, 429220]

private theorem split9Transition8 :
    extendTable 54 9 split9Table7 = split9Table8 := by rfl

private theorem split9Stage8 : countTable [9, 9, 9, 9, 9, 9, 9, 9] 54 = split9Table8 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9] 54) = split9Table8
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage7) split9Transition8

private def split9Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24310, 43749, 75501, 125565, 202005, 315315, 478731,
   708444, 1023660, 1446445, 2001285, 2714319, 3612231, 4720815, 6063255, 7658190, 9517662,
   11645073, 14033305, 16663185, 19502505, 22505751, 25614639, 28759500, 31861500, 34835625,
   37594305, 40051495, 42126975, 43750575, 44865975, 45433800, 45433800, 44865975, 43750575,
   42126975, 40051495, 37594305, 34835625, 31861500, 28759500, 25614639, 22505751, 19502505,
   16663185, 14033305]

private theorem split9Transition9 :
    extendTable 54 9 split9Table8 = split9Table9 := by rfl

private theorem split9Stage9 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9] 54 = split9Table9 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9] 54) = split9Table9
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage8) split9Transition9

private def split9Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620, 92368, 167860, 293380, 495220, 810040,
   1287484, 1992925, 3010150, 4443725, 6420700, 9091270, 12628000, 17223250, 23084500, 30427375,
   39466306, 50402935, 63412580, 78629320, 96130540, 115921972, 137924380, 161963065, 187761310,
   214938745, 243015388, 271421810, 299515480, 326602870, 351966340, 374894389, 394713550,
   410820025, 422709100, 430000450, 432457640, 430000450, 422709100, 410820025, 394713550,
   374894389, 351966340, 326602870, 299515480, 271421810]

private theorem split9Transition10 :
    extendTable 54 9 split9Table9 = split9Table10 := by rfl

private theorem split9Stage10 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54 = split9Table10 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9, 9] 54) = split9Table10
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage9) split9Transition10

private def split9Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92378, 184745, 352595, 645920, 1140920, 1950245,
   3235727, 5223647, 8222357, 12641772, 19013852, 28012754, 40472894, 57402764, 79992044, 109609379,
   147788201, 196198211, 256600641, 330786236, 420496076, 527326778, 652623158, 797362973,
   962039783, 1146551153, 1350100235, 1571119110, 1807222010, 2055195560, 2311031360, 2570003777,
   2826792947, 3075649907, 3310597697, 3525659402, 3715101654, 3873680294, 3996873914, 4081091069,
   4123838279, 4123838279, 4081091069, 3996873914, 3873680294, 3715101654]

private theorem split9Transition11 :
    extendTable 54 9 split9Table10 = split9Table11 := by rfl

private theorem split9Stage11 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54 = split9Table11 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54) = split9Table11
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage10) split9Transition11

private def split9Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31824, 75582, 167960, 352704, 705288, 1351142, 2491776,
   4441020, 7673744, 12889383, 21092292, 33690306, 52611780, 80439789, 120560088, 177316932,
   256168056, 363827190, 508379664, 699354228, 947732512, 1265876976, 1667359200, 2166673224,
   2778823488, 3518783697, 4400831436, 5437773210, 6640085244, 8015006143, 9565627512, 11290036836,
   13180572120, 15223249119, 17397418908, 19675705842, 22024263756, 24403372005, 26768373424,
   29070934608, 31260586512, 33286482021, 35099288940, 36653123442, 37907421564, 38828645571,
   39391728168, 39581170420]

private theorem split9Transition12 :
    extendTable 54 9 split9Table11 = split9Table12 := by rfl

private theorem split9Stage12 : countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54 = split9Table12 := by
  change extendTable 54 9 (countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54) = split9Table12
  exact Eq.trans (congrArg (extendTable 54 9) split9Stage11) split9Transition12

private theorem split9Exact : splitByCompositions 9 = splitLattice 9 := by
  change Int.ofNat ((countTable [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9] 54).getD 54 0) = _
  calc
    _ = 39581170420 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 54 0) split9Stage12) rfl)
    _ = _ := by decide

/-! Dilation 10, split slice. -/

private def split10Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split10Stage0 : countTable [] 60 = split10Table0 := by rfl

private def split10Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split10Transition1 :
    extendTable 60 10 split10Table0 = split10Table1 := by rfl

private theorem split10Stage1 : countTable [10] 60 = split10Table1 := by
  change extendTable 60 10 (countTable [] 60) = split10Table1
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage0) split10Transition1

private def split10Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split10Transition2 :
    extendTable 60 10 split10Table1 = split10Table2 := by rfl

private theorem split10Stage2 : countTable [10, 10] 60 = split10Table2 := by
  change extendTable 60 10 (countTable [10] 60) = split10Table2
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage1) split10Transition2

private def split10Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 75, 82, 87, 90, 91, 90, 87, 82, 75, 66, 55, 45, 36, 28,
   21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0]

private theorem split10Transition3 :
    extendTable 60 10 split10Table2 = split10Table3 := by rfl

private theorem split10Stage3 : countTable [10, 10, 10] 60 = split10Table3 := by
  change extendTable 60 10 (countTable [10, 10] 60) = split10Table3
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage2) split10Transition3

private def split10Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 360, 439, 520, 600, 676, 745, 804, 850, 880, 891,
   880, 850, 804, 745, 676, 600, 520, 439, 360, 286, 220, 165, 120, 84, 56, 35, 20, 10, 4, 1, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split10Transition4 :
    extendTable 60 10 split10Table3 = split10Table4 := by rfl

private theorem split10Stage4 : countTable [10, 10, 10, 10] 60 = split10Table4 := by
  change extendTable 60 10 (countTable [10, 10, 10] 60) = split10Table4
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage3) split10Transition4

private def split10Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1360, 1795, 2305, 2885, 3526, 4215, 4935, 5665,
   6380, 7051, 7645, 8135, 8500, 8725, 8801, 8725, 8500, 8135, 7645, 7051, 6380, 5665, 4935, 4215,
   3526, 2885, 2305, 1795, 1360, 1001, 715, 495, 330, 210, 126, 70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0]

private theorem split10Transition5 :
    extendTable 60 10 split10Table4 = split10Table5 := by rfl

private theorem split10Stage5 : countTable [10, 10, 10, 10, 10] 60 = split10Table5 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10] 60) = split10Table5
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage4) split10Transition5

private def split10Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 2002, 3003, 4362, 6152, 8442, 11292, 14748, 18837, 23562,
   28897, 34782, 41118, 47762, 54537, 61242, 67662, 73578, 78777, 83062, 86262, 88242, 88913, 88242,
   86262, 83062, 78777, 73578, 67662, 61242, 54537, 47762, 41118, 34782, 28897, 23562, 18837, 14748,
   11292, 8442, 6152, 4362, 3003, 2002, 1287, 792, 462, 252, 126, 56, 21, 6, 1]

private theorem split10Transition6 :
    extendTable 60 10 split10Table5 = split10Table6 := by rfl

private theorem split10Stage6 : countTable [10, 10, 10, 10, 10, 10] 60 = split10Table6 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10] 60) = split10Table6
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage5) split10Transition6

private def split10Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8008, 12369, 18515, 26936, 38172, 52794, 71379,
   94479, 122584, 156079, 195195, 239954, 290129, 345219, 404439, 466725, 530754, 594979, 657679,
   717024, 771155, 818279, 856779, 885304, 902839, 908755, 902839, 885304, 856779, 818279, 771155,
   717024, 657679, 594979, 530754, 466725, 404439, 345219, 290129, 239954, 195195, 156079, 122584,
   94479, 71379, 52794, 38172, 26936, 18515, 12369, 8008]

private theorem split10Transition7 :
    extendTable 60 10 split10Table6 = split10Table7 := by rfl

private theorem split10Stage7 : countTable [10, 10, 10, 10, 10, 10, 10] 60 = split10Table7 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10] 60) = split10Table7
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage6) split10Transition7

private def split10Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11440, 19448, 31816, 50324, 77232, 115320, 167904,
   238821, 332376, 453244, 606320, 796510, 1028456, 1306216, 1632920, 2010423, 2438976, 2916936,
   3440536, 4003736, 4598176, 5213252, 5836336, 6453161, 7048336, 7605956, 8110272, 8546386,
   8900936, 9162736, 9323336, 9377467, 9323336, 9162736, 8900936, 8546386, 8110272, 7605956,
   7048336, 6453161, 5836336, 5213252, 4598176, 4003736, 3440536, 2916936, 2438976, 2010423,
   1632920, 1306216, 1028456, 796510]

private theorem split10Transition8 :
    extendTable 60 10 split10Table7 = split10Table8 := by rfl

private theorem split10Stage8 : countTable [10, 10, 10, 10, 10, 10, 10, 10] 60 = split10Table8 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10] 60) = split10Table8
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage7) split10Transition8

private def split10Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24310, 43758, 75573, 125889, 203085, 318285, 485859,
   723888, 1054548, 1504360, 2104245, 2889315, 3898323, 5172723, 6755319, 8688510, 11012166,
   13761198, 16962913, 20634273, 24779205, 29386137, 34425963, 39850668, 45592788, 51565824,
   57665673, 63773083, 69757083, 75479283, 80798883, 85578174, 89688258, 93014658, 95462433,
   96960483, 97464799, 96960483, 95462433, 93014658, 89688258, 85578174, 80798883, 75479283,
   69757083, 63773083, 57665673, 51565824, 45592788, 39850668, 34425963, 29386137]

private theorem split10Transition9 :
    extendTable 60 10 split10Table8 = split10Table9 := by rfl

private theorem split10Stage9 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10] 60 = split10Table9 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10] 60) = split10Table9
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage8) split10Transition9

private def split10Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620, 92378, 167950, 293830, 496870, 814990,
   1300354, 2022955, 3074500, 4572425, 6663800, 9528805, 13383370, 18480520, 25109950, 33595375,
   44289256, 57564595, 73803620, 93383345, 116658190, 143940082, 175476730, 211429075, 251849140,
   296659645, 345636808, 398397725, 454393610, 512909980, 573074590, 633873559, 694175680,
   752764375, 808376140, 859743835, 905642810, 944937620, 976626970, 999884545, 1014093520,
   1018872811, 1014093520, 999884545, 976626970, 944937620, 905642810, 859743835, 808376140,
   752764375, 694175680, 633873559]

private theorem split10Transition10 :
    extendTable 60 10 split10Table9 = split10Table10 := by rfl

private theorem split10Stage10 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60 = split10Table10 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10, 10] 60) = split10Table10
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage9) split10Transition10

private def split10Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92378, 184756, 352705, 646525, 1143340, 1958110,
   3257749, 5278702, 8348197, 12909182, 19548672, 29028857, 42319849, 60632419, 85448539, 118547044,
   162021310, 218285551, 290066216, 380375061, 492460826, 629737108, 795685033, 993730738,
   1227099358, 1498649053, 1810690486, 2164798955, 2561627970, 3000734330, 3480425575, 3997640944,
   4547876542, 5125164187, 5722111252, 6330005947, 6938989112, 7538289924, 8116519169, 8662010104,
   9163193644, 9608991865, 9989211826, 10294920691, 10518783286, 10655344766, 10701243741,
   10655344766, 10518783286, 10294920691, 9989211826, 9608991865]

private theorem split10Transition11 :
    extendTable 60 10 split10Table10 = split10Table11 := by rfl

private theorem split10Stage11 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60 = split10Table11 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60) = split10Table11
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage10) split10Transition11

private def split10Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31824, 75582, 167960, 352716, 705420, 1351934, 2495208,
   4453032, 7709780, 12985479, 21325668, 34215402, 53720316, 82656795, 124791888, 185071602,
   269873616, 387277320, 547340520, 762368322, 1047155836, 1419182700, 1898734344, 2508922780,
   3275578956, 4226989845, 5393456784, 6806657298, 8498800740, 10501578385, 12844920804,
   15555588918, 18655639432, 22160819550, 26078958984, 30408438138, 35136818652, 40239725241,
   45680065300, 51407664738, 57359384952, 63459767086, 69622226400, 75750792690, 81742363572,
   87489407721, 92883026820, 97816260334, 102187498128, 105903853782, 108884347144, 111062748666,
   112389950388, 112835748609]

private theorem split10Transition12 :
    extendTable 60 10 split10Table11 = split10Table12 := by rfl

private theorem split10Stage12 : countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60 = split10Table12 := by
  change extendTable 60 10 (countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60) = split10Table12
  exact Eq.trans (congrArg (extendTable 60 10) split10Stage11) split10Transition12

private theorem split10Exact : splitByCompositions 10 = splitLattice 10 := by
  change Int.ofNat ((countTable [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10] 60).getD 60 0) = _
  calc
    _ = 112835748609 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 60 0) split10Stage12) rfl)
    _ = _ := by decide

/-! Dilation 11, split slice. -/

private def split11Table0 : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]

private theorem split11Stage0 : countTable [] 66 = split11Table0 := by rfl

private def split11Table1 : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0]

private theorem split11Transition1 :
    extendTable 66 11 split11Table0 = split11Table1 := by rfl

private theorem split11Stage1 : countTable [11] 66 = split11Table1 := by
  change extendTable 66 11 (countTable [] 66) = split11Table1
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage0) split11Transition1

private def split11Table2 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0]

private theorem split11Transition2 :
    extendTable 66 11 split11Table1 = split11Table2 := by rfl

private theorem split11Stage2 : countTable [11, 11] 66 = split11Table2 := by
  change extendTable 66 11 (countTable [11] 66) = split11Table2
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage1) split11Transition2

private def split11Table3 : List Nat :=
  [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 88, 96, 102, 106, 108, 108, 106, 102, 96, 88, 78,
   66, 55, 45, 36, 28, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split11Transition3 :
    extendTable 66 11 split11Table2 = split11Table3 := by rfl

private theorem split11Stage3 : countTable [11, 11, 11] 66 = split11Table3 := by
  change extendTable 66 11 (countTable [11, 11] 66) = split11Table3
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage2) split11Transition3

private def split11Table4 : List Nat :=
  [1, 4, 10, 20, 35, 56, 84, 120, 165, 220, 286, 364, 451, 544, 640, 736, 829, 916, 994, 1060, 1111,
   1144, 1156, 1144, 1111, 1060, 994, 916, 829, 736, 640, 544, 451, 364, 286, 220, 165, 120, 84, 56,
   35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split11Transition4 :
    extendTable 66 11 split11Table3 = split11Table4 := by rfl

private theorem split11Stage4 : countTable [11, 11, 11, 11] 66 = split11Table4 := by
  change extendTable 66 11 (countTable [11, 11, 11] 66) = split11Table4
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage3) split11Transition4

private def split11Table5 : List Nat :=
  [1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1365, 1815, 2355, 2985, 3701, 4495, 5355, 6265,
   7205, 8151, 9075, 9945, 10725, 11385, 11901, 12255, 12435, 12435, 12255, 11901, 11385, 10725,
   9945, 9075, 8151, 7205, 6265, 5355, 4495, 3701, 2985, 2355, 1815, 1365, 1001, 715, 495, 330, 210,
   126, 70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem split11Transition5 :
    extendTable 66 11 split11Table4 = split11Table5 := by rfl

private theorem split11Stage5 : countTable [11, 11, 11, 11, 11] 66 = split11Table5 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11] 66) = split11Table5
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage4) split11Transition5

private def split11Table6 : List Nat :=
  [1, 6, 21, 56, 126, 252, 462, 792, 1287, 2002, 3003, 4368, 6182, 8532, 11502, 15168, 19593, 24822,
   30877, 37752, 45408, 53768, 62712, 72072, 81642, 91188, 100458, 109192, 117132, 124032, 129668,
   133848, 136422, 137292, 136422, 133848, 129668, 124032, 117132, 109192, 100458, 91188, 81642,
   72072, 62712, 53768, 45408, 37752, 30877, 24822, 19593, 15168, 11502, 8532, 6182, 4368, 3003,
   2002, 1287, 792, 462, 252, 126, 56, 21, 6, 1]

private theorem split11Transition6 :
    extendTable 66 11 split11Table5 = split11Table6 := by rfl

private theorem split11Stage6 : countTable [11, 11, 11, 11, 11, 11] 66 = split11Table6 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11] 66) = split11Table6
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage5) split11Transition6

private def split11Table7 : List Nat :=
  [1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8008, 12376, 18557, 27083, 38564, 53676, 73143,
   97713, 128128, 165088, 209209, 260975, 320684, 388388, 463848, 546504, 635460, 729484, 827023,
   926233, 1025024, 1121120, 1212134, 1295658, 1369368, 1431144, 1479170, 1512014, 1528688, 1528688,
   1512014, 1479170, 1431144, 1369368, 1295658, 1212134, 1121120, 1025024, 926233, 827023, 729484,
   635460, 546504, 463848, 388388, 320684, 260975, 209209, 165088, 128128, 97713, 73143, 53676,
   38564, 27083, 18557, 12376]

private theorem split11Transition7 :
    extendTable 66 11 split11Table6 = split11Table7 := by rfl

private theorem split11Stage7 : countTable [11, 11, 11, 11, 11, 11, 11] 66 = split11Table7 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11] 66) = split11Table7
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage6) split11Transition7

private def split11Table8 : List Nat :=
  [1, 8, 36, 120, 330, 792, 1716, 3432, 6435, 11440, 19448, 31824, 50380, 77456, 115992, 169584,
   242517, 339768, 466972, 630344, 836550, 1092520, 1405196, 1781208, 2226499, 2745920, 3342816,
   4018624, 4772504, 5601024, 6497920, 7453952, 8456877, 9491560, 10540244, 11583000, 12598322,
   13563832, 14457060, 15256264, 15941255, 16494192, 16900312, 17148560, 17232084, 17148560,
   16900312, 16494192, 15941255, 15256264, 14457060, 13563832, 12598322, 11583000, 10540244,
   9491560, 8456877, 7453952, 6497920, 5601024, 4772504, 4018624, 3342816, 2745920, 2226499,
   1781208, 1405196]

private theorem split11Transition8 :
    extendTable 66 11 split11Table7 = split11Table8 := by rfl

private theorem split11Stage8 : countTable [11, 11, 11, 11, 11, 11, 11, 11] 66 = split11Table8 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11, 11] 66) = split11Table8
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage7) split11Transition8

private def split11Table9 : List Nat :=
  [1, 9, 45, 165, 495, 1287, 3003, 6435, 12870, 24310, 43758, 75582, 125961, 203409, 319365, 488829,
   731016, 1069992, 1535248, 2162160, 2992275, 4073355, 5459103, 7208487, 9384606, 12053070,
   15279894, 19128934, 23658921, 28920177, 34951125, 41774733, 49395060, 57794100, 66929148,
   76730940, 87102763, 97920675, 109034919, 120272559, 131441310, 142334478, 152736870, 162431478,
   171206685, 178863685, 185223753, 190134945, 193477878, 195170310, 195170310, 193477878,
   190134945, 185223753, 178863685, 171206685, 162431478, 152736870, 142334478, 131441310,
   120272559, 109034919, 97920675, 87102763, 76730940, 66929148, 57794100]

private theorem split11Transition9 :
    extendTable 66 11 split11Table8 = split11Table9 := by rfl

private theorem split11Stage9 : countTable [11, 11, 11, 11, 11, 11, 11, 11, 11] 66 = split11Table9 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11, 11, 11] 66) = split11Table9
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage8) split11Transition9

private def split11Table10 : List Nat :=
  [1, 10, 55, 220, 715, 2002, 5005, 11440, 24310, 48620, 92378, 167960, 293920, 497320, 816640,
   1305304, 2035825, 3104530, 4636775, 6792500, 9771905, 13820950, 19236295, 26369200, 35627845,
   47477506, 62438035, 81078140, 104006045, 131856230, 165272107, 204884680, 251287465, 305008210,
   366478255, 436000708, 513718865, 599586470, 693341495, 794485120, 902267509, 1015681810,
   1133467555, 1254124300, 1375935925, 1497005510, 1615300115, 1728704120, 1835079235, 1932328870,
   2018464261, 2091669580, 2150363215, 2193252490, 2219379305, 2228154512, 2219379305, 2193252490,
   2150363215, 2091669580, 2018464261, 1932328870, 1835079235, 1728704120, 1615300115, 1497005510,
   1375935925]

private theorem split11Transition10 :
    extendTable 66 11 split11Table9 = split11Table10 := by rfl

private theorem split11Stage10 : countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66 = split11Table10 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11, 11, 11, 11] 66) = split11Table10
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage9) split11Transition10

private def split11Table11 : List Nat :=
  [1, 11, 66, 286, 1001, 3003, 8008, 19448, 43758, 92378, 184756, 352716, 646635, 1143945, 1960530,
   3265614, 5300724, 8403252, 13035022, 19816082, 29563677, 43336007, 62479924, 88681164, 124015089,
   170995275, 232616670, 312389506, 414359726, 543111426, 703746758, 901838938, 1143354498,
   1434541758, 1781783718, 2191415226, 2669506246, 3221615210, 3852518670, 4565925650, 5364187114,
   6248012694, 7216208142, 8265447762, 9390096222, 10582093522, 11830915382, 13123618794,
   14444979164, 15777721564, 17102844330, 18400028790, 19648124496, 20825695176, 21911606926,
   22885637138, 23729080518, 24425327498, 24960390598, 25323356058, 25506741084, 25506741084,
   25323356058, 24960390598, 24425327498, 23729080518, 22885637138]

private theorem split11Transition11 :
    extendTable 66 11 split11Table10 = split11Table11 := by rfl

private theorem split11Stage11 : countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66 = split11Table11 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66) = split11Table11
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage10) split11Transition11

private def split11Table12 : List Nat :=
  [1, 12, 78, 364, 1365, 4368, 12376, 31824, 75582, 167960, 352716, 705432, 1352066, 2496000,
   4456464, 7721792, 13021515, 21421764, 34448778, 54245412, 83765331, 127008960, 189304128,
   277632576, 401001030, 570852360, 801508500, 1110632392, 1519691394, 2054399568, 2745111304,
   3627134160, 4740924981, 6132130732, 7851434526, 9954168588, 12499659745, 15550279680,
   19170181680, 23423717824, 28373545212, 34078446480, 40590907864, 47954516688, 56201258412,
   65348810176, 75397941840, 86330145408, 98105618326, 110661724680, 123912050340, 137746153480,
   152030090862, 166607773344, 181303172128, 195923361504, 210262345800, 224105579776, 237235054992,
   249434792256, 260496554176, 270225573696, 278446085424, 285006447232, 289783650234, 292687035576,
   293661065788]

private theorem split11Transition12 :
    extendTable 66 11 split11Table11 = split11Table12 := by rfl

private theorem split11Stage12 : countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66 = split11Table12 := by
  change extendTable 66 11 (countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66) = split11Table12
  exact Eq.trans (congrArg (extendTable 66 11) split11Stage11) split11Transition12

private theorem split11Exact : splitByCompositions 11 = splitLattice 11 := by
  change Int.ofNat ((countTable [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] 66).getD 66 0) = _
  calc
    _ = 293661065788 := congrArg Int.ofNat (Eq.trans (congrArg (fun row => row.getD 66 0) split11Stage12) rfl)
    _ = _ := by decide

theorem splitSamplesAgree (q : Nat) (hq : q ≤ 11) :
    splitByCompositions q = splitLattice q := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact split0Exact
  · exact split1Exact
  · exact split2Exact
  · exact split3Exact
  · exact split4Exact
  · exact split5Exact
  · exact split6Exact
  · exact split7Exact
  · exact split8Exact
  · exact split9Exact
  · exact split10Exact
  · exact split11Exact

private theorem numerator_count_congr (d : Nat) (f g : Nat → Int)
    (h : ∀ q ≤ d, f q = g q) : ehrhartNumerator d f = ehrhartNumerator d g := by
  unfold ehrhartNumerator
  apply List.map_congr_left
  intro k hk
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  rw [h (k - j) ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ (List.mem_range.mp hk)))]

theorem unsplitCompositionCertificate :
    ehrhartNumerator 10 unsplitByCompositions = unsplitCoefficients :=
  (numerator_count_congr 10 _ _ unsplitSamplesAgree).trans unsplitEhrhartCertificate

theorem splitCompositionCertificate :
    ehrhartNumerator 11 splitByCompositions = splitCoefficients :=
  (numerator_count_congr 11 _ _ splitSamplesAgree).trans splitEhrhartCertificate

/-- The numerators obtained directly from bounded compositions cannot have alternating
root lists. The dimension bound used to complete the Ehrhart numerator is external. -/
theorem compositionRowsDoNotInterlace :
    ¬ ∃ ps qs : List ℝ,
      (∀ x : ℝ, x ∈ ps ↔ evalAsc (ehrhartNumerator 10 unsplitByCompositions) x = 0) ∧
      (∀ x : ℝ, x ∈ qs ↔ evalAsc (ehrhartNumerator 11 splitByCompositions) x = 0) ∧
      alternatingRoots ps qs := by
  have hp : ehrhartNumerator 10 unsplitByCompositions = ehrhartNumerator 10 unsplitLattice :=
    numerator_count_congr 10 _ _ unsplitSamplesAgree
  have hq : ehrhartNumerator 11 splitByCompositions = ehrhartNumerator 11 splitLattice :=
    numerator_count_congr 11 _ _ splitSamplesAgree
  rw [hp, hq]
  exact computedRowsDoNotInterlace

#print axioms unsplitSamplesAgree
#print axioms splitSamplesAgree
#print axioms compositionRowsDoNotInterlace

end PrismSplit
