(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_34,
  catalog title "longestIncreasingSubsequence": an executable patience-sorting
  scan with lower-bound binary search computes the length of a longest strictly
  increasing integer subsequence, with a total precondition and exhaustive-
  subsequence maximality postcondition. This file contains no proof.
*)

let longestIncreasingSubsequence_precond = new_definition
  `longestIncreasingSubsequence_precond (nums:int list) <=> T`;;

let longestIncreasingSubsequence_get =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        longestIncreasingSubsequence_get 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!index:num. !xs:int list.
        longestIncreasingSubsequence_get (SUC index) xs =
        if xs = [] then (&0:int)
        else longestIncreasingSubsequence_get index (TL xs))`;;

let longestIncreasingSubsequence_setRaw =
  new_recursive_definition list_RECURSION
    `(!index:num. !value:int.
        longestIncreasingSubsequence_setRaw
          index value ([]:int list) = []) /\
     (!x:int. !xs:int list. !index:num. !value:int.
        longestIncreasingSubsequence_setRaw
          index value (CONS x xs) =
        if index = 0 then CONS value xs
        else
          CONS x
            (longestIncreasingSubsequence_setRaw
              (index - 1) value xs))`;;

let longestIncreasingSubsequence_set = new_definition
  `longestIncreasingSubsequence_set
      (index:num) (value:int) (xs:int list) =
     if index < LENGTH xs then
       longestIncreasingSubsequence_setRaw index value xs
     else xs`;;

let longestIncreasingSubsequence_binarySearchFuel =
  new_recursive_definition num_RECURSION
    `(!sub:int list. !num:int. !left:num. !right:num.
        longestIncreasingSubsequence_binarySearchFuel
          0 sub num left right = left) /\
     (!fuel:num. !sub:int list. !num:int.
      !left:num. !right:num.
        longestIncreasingSubsequence_binarySearchFuel
          (SUC fuel) sub num left right =
        if left < right then
          let mid = (left + right) DIV 2 in
          if longestIncreasingSubsequence_get mid sub = num then
            longestIncreasingSubsequence_binarySearchFuel
              fuel sub num left mid
          else if
            longestIncreasingSubsequence_get mid sub < num
          then
            longestIncreasingSubsequence_binarySearchFuel
              fuel sub num (mid + 1) right
          else
            longestIncreasingSubsequence_binarySearchFuel
              fuel sub num left mid
        else left)`;;

let binarySearchLeft = new_definition
  `binarySearchLeft
      (sub:int list) (num:int) (left:num) (right:num) =
     longestIncreasingSubsequence_binarySearchFuel
       (right - left) sub num left right`;;

let longestIncreasingSubsequence_scan =
  new_recursive_definition list_RECURSION
    `(!sub:int list.
        longestIncreasingSubsequence_scan
          ([]:int list) sub = sub) /\
     (!num:int. !nums:int list. !sub:int list.
        longestIncreasingSubsequence_scan
          (CONS num nums) sub =
        if
          num >
            longestIncreasingSubsequence_get
              (LENGTH sub - 1) sub
        then
          longestIncreasingSubsequence_scan
            nums (APPEND sub (CONS num []))
        else
          let left =
            binarySearchLeft
              sub num 0 (LENGTH sub - 1) in
          longestIncreasingSubsequence_scan
            nums
            (longestIncreasingSubsequence_set
              left num sub))`;;

let longestIncreasingSubsequence = new_definition
  `longestIncreasingSubsequence (nums:int list) =
     if nums = [] then (&0:int)
     else
       (&(LENGTH
          (longestIncreasingSubsequence_scan
            (TL nums) (CONS (HD nums) []))):int)`;;

let longestIncreasingSubsequence_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        longestIncreasingSubsequence_subseqFold
          ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        longestIncreasingSubsequence_subseqFold
          (CONS x xs) acc =
        longestIncreasingSubsequence_subseqFold
          xs
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
        longestIncreasingSubsequence_pairwiseIncreasing
          (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        longestIncreasingSubsequence_pairwiseIncreasing xs)`;;

let longestIncreasingSubsequence_postcond = new_definition
  `longestIncreasingSubsequence_postcond
      (nums:int list) (result:int) <=>
     let allSubseq =
       longestIncreasingSubsequence_allSubseq nums in
     let increasingSubseqLens =
       MAP (\l:int list. (&(LENGTH l):int))
         (FILTER
           longestIncreasingSubsequence_pairwiseIncreasing
           allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:int. k <= result) increasingSubseqLens`;;

let longestIncreasingSubsequence_spec_satisfied =
  `!nums:int list.
     longestIncreasingSubsequence_precond nums
     ==> longestIncreasingSubsequence_postcond
           nums (longestIncreasingSubsequence nums)`;;
