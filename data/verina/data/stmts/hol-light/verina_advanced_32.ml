(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_32,
  catalog title "longestIncreasingSubsequence": an executable dynamic-programming
  scan computes the length of a longest strictly increasing integer subsequence,
  with its total precondition and exhaustive-subsequence maximality postcondition.
  This file contains no proof.
*)

let longestIncreasingSubsequence_precond = new_definition
  `longestIncreasingSubsequence_precond (numbers:int list) <=> T`;;

let longestIncreasingSubsequence_findMaxLength =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubsequence_findMaxLength ([]:num list) = 0) /\
     (!x:num. !xs:num list.
        longestIncreasingSubsequence_findMaxLength (CONS x xs) =
        let maxRest =
          longestIncreasingSubsequence_findMaxLength xs in
        if x > maxRest then x else maxRest)`;;

let longestIncreasingSubsequence_findLengthEndingAtCurr =
  new_recursive_definition list_RECURSION
    `(!currNum:int. !lengths:num list. !best:num.
        longestIncreasingSubsequence_findLengthEndingAtCurr
          currNum ([]:int list) lengths best = best) /\
     (!prevVal:int. !restVals:int list. !currNum:int.
      !lengths:num list. !best:num.
        longestIncreasingSubsequence_findLengthEndingAtCurr
          currNum (CONS prevVal restVals) lengths best =
        if lengths = [] then best
        else
          let prevLen = HD lengths in
          let restLens = TL lengths in
          if prevVal < currNum then
            longestIncreasingSubsequence_findLengthEndingAtCurr
              currNum restVals restLens
              (if best >= prevLen then best else prevLen)
          else
            longestIncreasingSubsequence_findLengthEndingAtCurr
              currNum restVals restLens best)`;;

let longestIncreasingSubsequence_buildTables =
  new_recursive_definition list_RECURSION
    `(!prevNums:int list. !lengths:num list. !idx:num.
        longestIncreasingSubsequence_buildTables
          ([]:int list) prevNums lengths idx =
        longestIncreasingSubsequence_findMaxLength lengths) /\
     (!currNum:int. !restNums:int list. !prevNums:int list.
      !lengths:num list. !idx:num.
        longestIncreasingSubsequence_buildTables
          (CONS currNum restNums) prevNums lengths idx =
        let bestPrevLen =
          longestIncreasingSubsequence_findLengthEndingAtCurr
            currNum prevNums lengths 0 in
        let currLength = bestPrevLen + 1 in
        longestIncreasingSubsequence_buildTables
          restNums
          (APPEND prevNums (CONS currNum []))
          (APPEND lengths (CONS currLength []))
          (idx + 1))`;;

let longestIncreasingSubsequence = new_definition
  `longestIncreasingSubsequence (numbers:int list) =
     if numbers = [] then 0
     else if TL numbers = [] then 1
     else
       longestIncreasingSubsequence_buildTables
         (TL numbers) (CONS (HD numbers) [])
         (CONS 1 []) 1`;;

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
  `longestIncreasingSubsequence_allSubseq (numbers:int list) =
     MAP REVERSE
       (longestIncreasingSubsequence_subseqFold
         numbers (CONS ([]:int list) []))`;;

let longestIncreasingSubsequence_pairwiseIncreasing =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubsequence_pairwiseIncreasing
        ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        longestIncreasingSubsequence_pairwiseIncreasing
          (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        longestIncreasingSubsequence_pairwiseIncreasing xs)`;;

let longestIncreasingSubsequence_postcond = new_definition
  `longestIncreasingSubsequence_postcond
      (numbers:int list) (result:num) <=>
     let allSubseq =
       longestIncreasingSubsequence_allSubseq numbers in
     let increasingSubseqLens =
       MAP (\l:int list. LENGTH l)
         (FILTER
           longestIncreasingSubsequence_pairwiseIncreasing
           allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:num. k <= result) increasingSubseqLens`;;

let longestIncreasingSubsequence_spec_satisfied =
  `!numbers:int list.
     longestIncreasingSubsequence_precond numbers
     ==> longestIncreasingSubsequence_postcond numbers
           (longestIncreasingSubsequence numbers)`;;
