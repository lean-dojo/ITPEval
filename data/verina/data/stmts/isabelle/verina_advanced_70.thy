(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_70,
  catalog title "semiOrderedPermutation": an executable index-based program
  computes the adjacent swaps needed to put 1 first and the list length last
  in a nonempty integer permutation, together with its precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_advanced_70
  imports Main
begin

fun semiOrderedPermutation_idxOf ::
    "int list \<Rightarrow> int \<Rightarrow> nat" where
  "semiOrderedPermutation_idxOf [] value = 0"
| "semiOrderedPermutation_idxOf (x # xs) value =
    (if x = value
     then 0
     else Suc (semiOrderedPermutation_idxOf xs value))"

definition semiOrderedPermutation_precond ::
    "int list \<Rightarrow> bool" where
  "semiOrderedPermutation_precond nums \<longleftrightarrow>
    (let n = length nums
     in n > 0 \<and>
        distinct nums \<and>
        list_all (\<lambda>x. 1 \<le> x \<and> x \<le> int n) nums)"

definition semiOrderedPermutation :: "int list \<Rightarrow> int" where
  "semiOrderedPermutation nums =
    (let lengthList = length nums;
         numOne = (1 :: int);
         largestNum = int lengthList;
         firstIndex = semiOrderedPermutation_idxOf nums numOne;
         lastIndex = semiOrderedPermutation_idxOf nums largestNum;
         startPosition = 0;
         endPosition = lengthList - 1;
         shouldMoveOne = (firstIndex \<noteq> startPosition);
         shouldMoveLast = (lastIndex \<noteq> endPosition);
         distanceOne = (if shouldMoveOne then firstIndex else 0);
         distanceLast =
           (if shouldMoveLast then endPosition - lastIndex else 0);
         totalMoves = distanceOne + distanceLast;
         needAdjustment = (firstIndex > lastIndex);
         adjustedMoves =
           (if needAdjustment then totalMoves - 1 else totalMoves)
     in int adjustedMoves)"

definition semiOrderedPermutation_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "semiOrderedPermutation_postcond nums result \<longleftrightarrow>
    (let n = length nums;
         pos1 = semiOrderedPermutation_idxOf nums 1;
         posn = semiOrderedPermutation_idxOf nums (int n)
     in if pos1 > posn
        then int (pos1 + n) = result + 2 + int posn
        else int (pos1 + n) = result + 1 + int posn)"

theorem semiOrderedPermutation_spec_satisfied:
  assumes "semiOrderedPermutation_precond nums"
  shows
    "semiOrderedPermutation_postcond
      nums (semiOrderedPermutation nums)"
  sorry

end
