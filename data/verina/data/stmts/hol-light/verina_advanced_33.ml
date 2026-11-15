(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_33,
  catalog title "longestIncreasingSubsequence": an executable include-or-skip
  recursion computes the length of a longest strictly increasing integer
  subsequence, with a total precondition and exhaustive-subsequence
  maximality postcondition. This file contains no proof.
*)

let longestIncreasingSubsequence_precond = new_definition
  `longestIncreasingSubsequence_precond (nums:int list) <=> T`;;

let longestIncreasingSubsequence_max2 = new_definition
  `longestIncreasingSubsequence_max2 (a:num) (b:num) =
     if a > b then a else b`;;

let longestIncreasingSubsequence_listLength =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubsequence_listLength ([]:int list) = 0) /\
     (!x:int. !xs:int list.
        longestIncreasingSubsequence_listLength (CONS x xs) =
        1 + longestIncreasingSubsequence_listLength xs)`;;

let longestIncreasingSubsequence_optionValue = new_definition
  `longestIncreasingSubsequence_optionValue (prev:int option) =
     @x:int. prev = SOME x`;;

let longestIncreasingSubsequence_helper =
  new_recursive_definition list_RECURSION
    `(!prev:int option.
        longestIncreasingSubsequence_helper ([]:int list) prev = 0) /\
     (!h:int. !t:int list. !prev:int option.
        longestIncreasingSubsequence_helper (CONS h t) prev =
        let canTake =
          if prev = NONE then T
          else longestIncreasingSubsequence_optionValue prev < h in
        let withTake =
          if canTake then
            1 + longestIncreasingSubsequence_helper t (SOME h)
          else 0 in
        let withoutTake =
          longestIncreasingSubsequence_helper t prev in
        longestIncreasingSubsequence_max2 withTake withoutTake)`;;

let longestIncreasingSubsequence = new_definition
  `longestIncreasingSubsequence (nums:int list) =
     longestIncreasingSubsequence_helper nums NONE`;;

let longestIncreasingSubsequence_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        longestIncreasingSubsequence_subseqFold [] acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        longestIncreasingSubsequence_subseqFold (CONS x xs) acc =
        longestIncreasingSubsequence_subseqFold xs
          (APPEND acc
            (MAP (\sub:int list. CONS x sub) acc)))`;;

let longestIncreasingSubsequence_allSubseq = new_definition
  `longestIncreasingSubsequence_allSubseq (nums:int list) =
     MAP REVERSE
       (longestIncreasingSubsequence_subseqFold
         nums (CONS ([]:int list) []))`;;

let longestIncreasingSubsequence_pairwiseIncreasing =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubsequence_pairwiseIncreasing
        ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        longestIncreasingSubsequence_pairwiseIncreasing (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        longestIncreasingSubsequence_pairwiseIncreasing xs)`;;

let longestIncreasingSubsequence_postcond = new_definition
  `longestIncreasingSubsequence_postcond
      (nums:int list) (result:num) <=>
     let allSubseq =
       longestIncreasingSubsequence_allSubseq nums in
     let increasingSubseqLens =
       MAP (\l:int list. LENGTH l)
         (FILTER
           longestIncreasingSubsequence_pairwiseIncreasing
           allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:num. k <= result) increasingSubseqLens`;;

let longestIncreasingSubsequence_spec_satisfied =
  `!nums:int list.
     longestIncreasingSubsequence_precond nums
     ==> longestIncreasingSubsequence_postcond nums
           (longestIncreasingSubsequence nums)`;;
