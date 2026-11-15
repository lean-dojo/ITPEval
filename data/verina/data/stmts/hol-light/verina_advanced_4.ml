(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_4,
  catalog title "LongestIncreasingSubsequence": an executable dynamic-
  programming array computation returns the length of a longest strictly
  increasing integer subsequence, with its total precondition and exhaustive-
  subsequence maximality postcondition. This file contains no proof.
*)

let LongestIncreasingSubsequence_precond = new_definition
  `LongestIncreasingSubsequence_precond (a:int list) <=> T`;;

let intMax = new_definition
  `intMax (x:int) (y:int) = if x < y then y else x`;;

let LongestIncreasingSubsequence_getInt =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        LongestIncreasingSubsequence_getInt 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!n:num. !xs:int list.
        LongestIncreasingSubsequence_getInt (SUC n) xs =
        if xs = [] then (&0:int)
        else LongestIncreasingSubsequence_getInt n (TL xs))`;;

let LongestIncreasingSubsequence_setInt =
  new_recursive_definition num_RECURSION
    `(!value:int. !xs:int list.
        LongestIncreasingSubsequence_setInt 0 value xs =
        if xs = [] then [] else CONS value (TL xs)) /\
     (!n:num. !value:int. !xs:int list.
        LongestIncreasingSubsequence_setInt (SUC n) value xs =
        if xs = [] then []
        else CONS (HD xs)
          (LongestIncreasingSubsequence_setInt n value (TL xs)))`;;

let LongestIncreasingSubsequence_fillInner =
  new_recursive_definition num_RECURSION
    `(!i:num. !a:int list. !dp:int list.
        LongestIncreasingSubsequence_fillInner 0 i a dp = dp) /\
     (!j:num. !i:num. !a:int list. !dp:int list.
        LongestIncreasingSubsequence_fillInner (SUC j) i a dp =
        let previous =
          LongestIncreasingSubsequence_fillInner j i a dp in
        if LongestIncreasingSubsequence_getInt j a <
             LongestIncreasingSubsequence_getInt i a
        then
          let newVal =
            intMax
              (LongestIncreasingSubsequence_getInt i previous)
              (LongestIncreasingSubsequence_getInt j previous + &1) in
          LongestIncreasingSubsequence_setInt i newVal previous
        else previous)`;;

let LongestIncreasingSubsequence_fillOuter =
  new_recursive_definition num_RECURSION
    `(!a:int list. !dp:int list.
        LongestIncreasingSubsequence_fillOuter 0 a dp = dp) /\
     (!k:num. !a:int list. !dp:int list.
        LongestIncreasingSubsequence_fillOuter (SUC k) a dp =
        let previous =
          LongestIncreasingSubsequence_fillOuter k a dp in
        let i = SUC k in
        LongestIncreasingSubsequence_fillInner i i a previous)`;;

let LongestIncreasingSubsequence_maxFold =
  new_recursive_definition list_RECURSION
    `(!acc:int.
        LongestIncreasingSubsequence_maxFold acc [] = acc) /\
     (!x:int. !xs:int list. !acc:int.
        LongestIncreasingSubsequence_maxFold acc (CONS x xs) =
        LongestIncreasingSubsequence_maxFold
          (intMax acc x) xs)`;;

let LongestIncreasingSubsequence = new_definition
  `LongestIncreasingSubsequence (a:int list) =
     let n = LENGTH a in
     let initialDp = REPLICATE n (&1:int) in
     let finalDp =
       LongestIncreasingSubsequence_fillOuter (n - 1) a initialDp in
     LongestIncreasingSubsequence_maxFold (&0:int) finalDp`;;

let LongestIncreasingSubsequence_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        LongestIncreasingSubsequence_subseqFold
          ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        LongestIncreasingSubsequence_subseqFold
          (CONS x xs) acc =
        LongestIncreasingSubsequence_subseqFold
          xs
          (APPEND acc
            (MAP (\sub:int list. CONS x sub) acc)))`;;

let LongestIncreasingSubsequence_allSubseq = new_definition
  `LongestIncreasingSubsequence_allSubseq (a:int list) =
     MAP REVERSE
       (LongestIncreasingSubsequence_subseqFold
         a (CONS ([]:int list) []))`;;

let LongestIncreasingSubsequence_pairwiseIncreasing =
  new_recursive_definition list_RECURSION
    `(LongestIncreasingSubsequence_pairwiseIncreasing
        ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        LongestIncreasingSubsequence_pairwiseIncreasing
          (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        LongestIncreasingSubsequence_pairwiseIncreasing xs)`;;

let LongestIncreasingSubsequence_postcond = new_definition
  `LongestIncreasingSubsequence_postcond
      (a:int list) (result:int) <=>
     let allSubseq =
       LongestIncreasingSubsequence_allSubseq a in
     let increasingSubseqLens =
       MAP (\l:int list. (&(LENGTH l):int))
         (FILTER
           LongestIncreasingSubsequence_pairwiseIncreasing
           allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:int. k <= result) increasingSubseqLens`;;

let LongestIncreasingSubsequence_spec_satisfied =
  `!a:int list.
     LongestIncreasingSubsequence_precond a
     ==> LongestIncreasingSubsequence_postcond
           a (LongestIncreasingSubsequence a)`;;
