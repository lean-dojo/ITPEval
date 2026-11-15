(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_31,
  catalog title "longestIncreasingSubseqLength": exhaustive subsequence
  generation, strict-increase filtering, and a maximum-length fold compute the
  length of a longest strictly increasing integer subsequence, with a total
  precondition and an independently enumerated maximality postcondition. This
  file contains no proof.
*)

let longestIncreasingSubseqLength_precond = new_definition
  `longestIncreasingSubseqLength_precond (xs:int list) <=> T`;;

let longestIncreasingSubseqLength_subsequences =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubseqLength_subsequences ([]:int list) =
        CONS ([]:int list) []) /\
     (!x:int. !xs:int list.
        longestIncreasingSubseqLength_subsequences (CONS x xs) =
        let subs = longestIncreasingSubseqLength_subsequences xs in
        APPEND subs (MAP (\s:int list. CONS x s) subs))`;;

let longestIncreasingSubseqLength_isStrictlyIncreasing =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubseqLength_isStrictlyIncreasing ([]:int list) <=>
        T) /\
     (!x:int. !xs:int list.
        longestIncreasingSubseqLength_isStrictlyIncreasing (CONS x xs) <=>
        if xs = [] then T
        else
          x < HD xs /\
          longestIncreasingSubseqLength_isStrictlyIncreasing xs)`;;

let longestIncreasingSubseqLength_maxFold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        longestIncreasingSubseqLength_maxFold acc [] = acc) /\
     (!s:int list. !ss:(int list)list. !acc:num.
        longestIncreasingSubseqLength_maxFold acc (CONS s ss) =
        longestIncreasingSubseqLength_maxFold
          (if acc >= LENGTH s then acc else LENGTH s) ss)`;;

let longestIncreasingSubseqLength = new_definition
  `longestIncreasingSubseqLength (xs:int list) =
     let subs = longestIncreasingSubseqLength_subsequences xs in
     let increasing =
       FILTER longestIncreasingSubseqLength_isStrictlyIncreasing subs in
     longestIncreasingSubseqLength_maxFold 0 increasing`;;

let longestIncreasingSubseqLength_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        longestIncreasingSubseqLength_subseqFold [] acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        longestIncreasingSubseqLength_subseqFold (CONS x xs) acc =
        longestIncreasingSubseqLength_subseqFold xs
          (APPEND acc (MAP (\sub:int list. CONS x sub) acc)))`;;

let longestIncreasingSubseqLength_allSubseq = new_definition
  `longestIncreasingSubseqLength_allSubseq (xs:int list) =
     MAP REVERSE
       (longestIncreasingSubseqLength_subseqFold xs
         (CONS ([]:int list) []))`;;

let longestIncreasingSubseqLength_pairwiseIncreasing =
  new_recursive_definition list_RECURSION
    `(longestIncreasingSubseqLength_pairwiseIncreasing ([]:int list) <=>
        T) /\
     (!x:int. !xs:int list.
        longestIncreasingSubseqLength_pairwiseIncreasing (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        longestIncreasingSubseqLength_pairwiseIncreasing xs)`;;

let longestIncreasingSubseqLength_postcond = new_definition
  `longestIncreasingSubseqLength_postcond
      (xs:int list) (result:num) <=>
     let allSubseq = longestIncreasingSubseqLength_allSubseq xs in
     let increasingSubseqLens =
       MAP (\l:int list. LENGTH l)
         (FILTER longestIncreasingSubseqLength_pairwiseIncreasing allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:num. k <= result) increasingSubseqLens`;;

let longestIncreasingSubseqLength_spec_satisfied =
  `!xs:int list.
     longestIncreasingSubseqLength_precond xs
     ==> longestIncreasingSubseqLength_postcond xs
           (longestIncreasingSubseqLength xs)`;;
