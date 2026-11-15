(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_25,
  catalog title "lengthOfLIS": an executable dynamic-programming array
  computation returns the length of a longest strictly increasing integer
  subsequence, with its total precondition and exhaustive-subsequence
  maximality postcondition. This file contains no proof.
*)

let lengthOfLIS_precond = new_definition
  `lengthOfLIS_precond (nums:int list) <=> T`;;

let lengthOfLIS_getInt =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        lengthOfLIS_getInt 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!n:num. !xs:int list.
        lengthOfLIS_getInt (SUC n) xs =
        if xs = [] then (&0:int)
        else lengthOfLIS_getInt n (TL xs))`;;

let lengthOfLIS_getNum =
  new_recursive_definition num_RECURSION
    `(!xs:num list.
        lengthOfLIS_getNum 0 xs =
        if xs = [] then 0 else HD xs) /\
     (!n:num. !xs:num list.
        lengthOfLIS_getNum (SUC n) xs =
        if xs = [] then 0
        else lengthOfLIS_getNum n (TL xs))`;;

let lengthOfLIS_setNum =
  new_recursive_definition num_RECURSION
    `(!value:num. !xs:num list.
        lengthOfLIS_setNum 0 value xs =
        if xs = [] then [] else CONS value (TL xs)) /\
     (!n:num. !value:num. !xs:num list.
        lengthOfLIS_setNum (SUC n) value xs =
        if xs = [] then []
        else CONS (HD xs)
          (lengthOfLIS_setNum n value (TL xs)))`;;

let lengthOfLIS_fillInner =
  new_recursive_definition num_RECURSION
    `(!i:num. !nums:int list. !dp:num list.
        lengthOfLIS_fillInner 0 i nums dp = dp) /\
     (!j:num. !i:num. !nums:int list. !dp:num list.
        lengthOfLIS_fillInner (SUC j) i nums dp =
        let previous =
          lengthOfLIS_fillInner j i nums dp in
        if lengthOfLIS_getInt j nums <
             lengthOfLIS_getInt i nums /\
           lengthOfLIS_getNum j previous + 1 >
             lengthOfLIS_getNum i previous
        then
          lengthOfLIS_setNum i
            (lengthOfLIS_getNum j previous + 1)
            previous
        else previous)`;;

let lengthOfLIS_fillOuter =
  new_recursive_definition num_RECURSION
    `(!nums:int list. !dp:num list.
        lengthOfLIS_fillOuter 0 nums dp = dp) /\
     (!k:num. !nums:int list. !dp:num list.
        lengthOfLIS_fillOuter (SUC k) nums dp =
        let previous =
          lengthOfLIS_fillOuter k nums dp in
        let i = SUC k in
        lengthOfLIS_fillInner i i nums previous)`;;

let lengthOfLIS_maxFold =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        lengthOfLIS_maxFold acc [] = acc) /\
     (!x:num. !xs:num list. !acc:num.
        lengthOfLIS_maxFold acc (CONS x xs) =
        lengthOfLIS_maxFold
          (if acc >= x then acc else x) xs)`;;

let maxInArray = new_definition
  `maxInArray (arr:num list) = lengthOfLIS_maxFold 0 arr`;;

let lengthOfLIS = new_definition
  `lengthOfLIS (nums:int list) =
     if nums = [] then 0
     else
       let n = LENGTH nums in
       let initialDp = REPLICATE n 1 in
       let finalDp =
         lengthOfLIS_fillOuter (n - 1) nums initialDp in
       maxInArray finalDp`;;

let lengthOfLIS_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        lengthOfLIS_subseqFold [] acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        lengthOfLIS_subseqFold (CONS x xs) acc =
        lengthOfLIS_subseqFold xs
          (APPEND acc
            (MAP (\sub:int list. CONS x sub) acc)))`;;

let lengthOfLIS_allSubseq = new_definition
  `lengthOfLIS_allSubseq (nums:int list) =
     MAP REVERSE
       (lengthOfLIS_subseqFold nums
         (CONS ([]:int list) []))`;;

let lengthOfLIS_strictlyIncreasing =
  new_recursive_definition list_RECURSION
    `(lengthOfLIS_strictlyIncreasing ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        lengthOfLIS_strictlyIncreasing (CONS x xs) <=>
        ALL (\y:int. x < y) xs /\
        lengthOfLIS_strictlyIncreasing xs)`;;

let lengthOfLIS_postcond = new_definition
  `lengthOfLIS_postcond (nums:int list) (result:num) <=>
     let allSubseq = lengthOfLIS_allSubseq nums in
     let increasingSubseqLens =
       MAP (\l:int list. LENGTH l)
         (FILTER lengthOfLIS_strictlyIncreasing allSubseq) in
     MEM result increasingSubseqLens /\
     ALL (\k:num. k <= result) increasingSubseqLens`;;

let lengthOfLIS_spec_satisfied =
  `!nums:int list.
     lengthOfLIS_precond nums
     ==> lengthOfLIS_postcond nums (lengthOfLIS nums)`;;
