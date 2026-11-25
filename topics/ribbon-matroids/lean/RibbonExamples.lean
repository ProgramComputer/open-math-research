import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.Basic

/-!
Finite rank and flat computations for particular small graphic ribbons.
The rank-three and rank-four KL degree bound leaves only a constant and a
linear term. The coefficient checks below verify the full KL defining identity
for every contraction by a flat, using the subset-sum characteristic polynomial.
-/

namespace RibbonExamples

set_option maxRecDepth 14000
set_option maxHeartbeats 4000000

abbrev Edge := Nat × Nat

structure Graph where
  vertices : Nat
  edges : List Edge

def subsets (G : Graph) : List Nat := List.range (2 ^ G.edges.length)

def edgeIndices (G : Graph) : List Nat := List.range G.edges.length

def selected (G : Graph) (mask : Nat) : List Edge :=
  (G.edges.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst

def merge (components : List Nat) (e : Edge) : List Nat :=
  let a := components[e.1]?.getD 0
  let b := components[e.2]?.getD 0
  components.map fun c => if c == b then a else c

def rank (G : Graph) (mask : Nat) : Nat :=
  let components := (selected G mask).foldl merge (List.range G.vertices)
  G.vertices - components.eraseDups.length

def isFlat (G : Graph) (mask : Nat) : Bool :=
  (edgeIndices G).all fun i =>
    mask.testBit i || rank G (mask ||| (2 ^ i)) > rank G mask

def below (f g : Nat) : Bool := f &&& g == f

structure RankTable where
  ranks : Array Nat
  flats : List Nat
  masks : List Nat
  size : Nat
  topRank : Nat

def table (G : Graph) : RankTable :=
  ⟨(subsets G).map (rank G) |>.toArray, (subsets G).filter (isFlat G),
    subsets G, G.edges.length, rank G (2 ^ G.edges.length - 1)⟩

def RankTable.r (T : RankTable) (mask : Nat) : Nat := T.ranks[mask]?.getD 0

def RankTable.contractionRank (T : RankTable) (f : Nat) : Nat := T.topRank - T.r f

def RankTable.flatsOver (T : RankTable) (f : Nat) : List Nat :=
  T.flats.filter fun j => below f j

def klLinear (T : RankTable) (f : Nat) : Int :=
  if T.contractionRank f < 3 then 0 else
    let flats := T.flatsOver f
    let hyperplanes := flats.filter fun j => T.r j + 1 == T.topRank
    let atoms := flats.filter fun j => T.r j == T.r f + 1
    (hyperplanes.length : Int) - (atoms.length : Int)

def signedSubsets (T : RankTable) (a : Nat) : Int :=
  if ((List.range T.size).filter fun i => a.testBit i).length % 2 == 0 then 1 else -1

def charCoeff (T : RankTable) (f j k : Nat) : Int :=
  (T.masks.foldl (fun accum a =>
    if below a j && (a &&& f == 0) && (T.r j - T.r (f ||| a) == k)
    then accum + signedSubsets T a else accum) 0)

def klLhs (T : RankTable) (f k : Nat) : Int :=
  if k == T.contractionRank f then 1
  else if k + 1 == T.contractionRank f then klLinear T f else 0

def klRhs (T : RankTable) (f k : Nat) : Int :=
  (T.flatsOver f).foldl (fun accum j =>
    accum + charCoeff T f j k +
      if k == 0 then 0 else charCoeff T f j (k - 1) * klLinear T j) 0

def checkKL (G : Graph) : Bool :=
  let T := table G
  T.flats.all fun f =>
    (klLinear T f == 0 || 2 < T.contractionRank f) &&
    (List.range (T.contractionRank f + 2)).all fun k => klLhs T f k == klRhs T f k

def zCoeffs (G : Graph) : List Int :=
  let T := table G
  (List.range (T.topRank + 1)).map fun k =>
    T.flats.foldl (fun accum f =>
      accum + if k == T.r f then 1 else if k == T.r f + 1 then klLinear T f else 0) 0

def narayana (n : Nat) : List Int :=
  (List.range n).map fun k => ((n.choose k * n.choose (k + 1)) / n : Nat)

def quadrilateral : Graph := ⟨4, [(0, 1), (1, 2), (2, 3), (0, 3)]⟩

def diamond : Graph := ⟨4, quadrilateral.edges ++ [(0, 2)]⟩

def doubledDiamond : Graph := ⟨4, diamond.edges ++ [(0, 2)]⟩

theorem quadrilateral_kl : checkKL quadrilateral = true := by decide

theorem diamond_kl : checkKL diamond = true := by decide

theorem doubledDiamond_kl : checkKL doubledDiamond = true := by decide

theorem diamond_coefficients : zCoeffs diamond = [1, 6, 6, 1] := by decide

theorem diamond_narayana : zCoeffs diamond = narayana 4 := by decide

theorem doubledDiamond_narayana : zCoeffs doubledDiamond = narayana 4 := by decide

theorem diamond_deletion : zCoeffs diamond = zCoeffs quadrilateral := by decide

#print axioms quadrilateral_kl
#print axioms diamond_kl
#print axioms doubledDiamond_kl
#print axioms diamond_narayana
#print axioms doubledDiamond_narayana
#print axioms diamond_deletion

end RibbonExamples
