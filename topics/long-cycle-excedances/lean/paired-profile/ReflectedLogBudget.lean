import ReflectedLogTail
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OpenMathResearch.LongCycleExcedances
open Finset

theorem reflected_log_low_budget :
    (1 + ∑' i, reflectedLogWeight (1/405) (i+1))/(2*(109/10)) ≤ 1/10 := by
  have h1 : reflectedLogWeight (1/405) 1 ≤ (934782:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h2 : reflectedLogWeight (1/405) 2 ≤ (203089:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h3 : reflectedLogWeight (1/405) 3 ≤ (35363:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h4 : reflectedLogWeight (1/405) 4 ≤ (4402:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h5 : reflectedLogWeight (1/405) 5 ≤ (385:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h6 : reflectedLogWeight (1/405) 6 ≤ (24:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h7 : reflectedLogWeight (1/405) 7 ≤ (2:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h8 : reflectedLogWeight (1/405) 8 ≤ (1:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h9 : reflectedLogWeight (1/405) 9 ≤ (1:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h10 : reflectedLogWeight (1/405) 10 ≤ (1:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h11 : reflectedLogWeight (1/405) 11 ≤ (1:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have htail : reflectedLogTailScale (1/405) 12 / 12^2 ≤ (1:ℝ)/1000000 := by
    norm_num [reflectedLogTailScale]
  have hs := (reflected_log_all (h:=1/405) (by norm_num) 11).2
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,Nat.cast_ofNat] at hs
  norm_num at htail
  apply (div_le_iff₀ (by norm_num)).mpr
  linarith only [hs,htail,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

#print axioms reflected_log_low_budget

theorem reflected_log_all_budget :
    (1 + ∑' i, reflectedLogWeight (1/1940) (i+1))/(2*(227/100)) ≤ 4/5 := by
  have h1 : reflectedLogWeight (1/1940) 1 ≤ (1358726:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h2 : reflectedLogWeight (1/1940) 2 ≤ (619545:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h3 : reflectedLogWeight (1/1940) 3 ≤ (322717:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h4 : reflectedLogWeight (1/1940) 4 ≤ (168111:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h5 : reflectedLogWeight (1/1940) 5 ≤ (84039:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h6 : reflectedLogWeight (1/1940) 6 ≤ (39602:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h7 : reflectedLogWeight (1/1940) 7 ≤ (17437:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h8 : reflectedLogWeight (1/1940) 8 ≤ (7142:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h9 : reflectedLogWeight (1/1940) 9 ≤ (2716:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h10 : reflectedLogWeight (1/1940) 10 ≤ (959:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have h11 : reflectedLogWeight (1/1940) 11 ≤ (314:ℝ)/1000000 := by
    norm_num [reflectedLogWeight]
  have htail : reflectedLogTailScale (1/1940) 12 / 12^2 ≤ (8679:ℝ)/1000000 := by
    norm_num [reflectedLogTailScale]
  have hs := (reflected_log_all (h:=1/1940) (by norm_num) 11).2
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,Nat.cast_ofNat] at hs
  norm_num at htail
  apply (div_le_iff₀ (by norm_num)).mpr
  linarith only [hs,htail,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

#print axioms reflected_log_all_budget

end OpenMathResearch.LongCycleExcedances
