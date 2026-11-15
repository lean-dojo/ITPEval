(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_3,
  catalog title "LongestCommonSubsequence": an executable dynamic-programming
  table computes the longest common subsequence length of two integer arrays,
  with its total precondition and maximality postcondition. This file contains
  no proof.
*)

let LongestCommonSubsequence_getInt =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        LongestCommonSubsequence_getInt 0 xs =
        if xs = [] then (&0:int) else HD xs) /\
     (!n:num. !xs:int list.
        LongestCommonSubsequence_getInt (SUC n) xs =
        if xs = [] then (&0:int)
        else LongestCommonSubsequence_getInt n (TL xs))`;;

let LongestCommonSubsequence_getRow =
  new_recursive_definition num_RECURSION
    `(!rows:(int list)list.
        LongestCommonSubsequence_getRow 0 rows =
        if rows = [] then [] else HD rows) /\
     (!n:num. !rows:(int list)list.
        LongestCommonSubsequence_getRow (SUC n) rows =
        if rows = [] then []
        else LongestCommonSubsequence_getRow n (TL rows))`;;

let LongestCommonSubsequence_setInt =
  new_recursive_definition num_RECURSION
    `(!value:int. !xs:int list.
        LongestCommonSubsequence_setInt 0 value xs =
        if xs = [] then [] else CONS value (TL xs)) /\
     (!n:num. !value:int. !xs:int list.
        LongestCommonSubsequence_setInt (SUC n) value xs =
        if xs = [] then []
        else CONS (HD xs)
          (LongestCommonSubsequence_setInt n value (TL xs)))`;;

let LongestCommonSubsequence_setRow =
  new_recursive_definition num_RECURSION
    `(!row:int list. !rows:(int list)list.
        LongestCommonSubsequence_setRow 0 row rows =
        if rows = [] then [] else CONS row (TL rows)) /\
     (!n:num. !row:int list. !rows:(int list)list.
        LongestCommonSubsequence_setRow (SUC n) row rows =
        if rows = [] then []
        else CONS (HD rows)
          (LongestCommonSubsequence_setRow n row (TL rows)))`;;

let intMax = new_definition
  `intMax (x:int) (y:int) = if x < y then y else x`;;

let LongestCommonSubsequence_fillRow =
  new_recursive_definition list_RECURSION
    `(!i:num. !j:num. !x:int. !dp:(int list)list.
        LongestCommonSubsequence_fillRow i j x [] dp = dp) /\
     (!y:int. !ys:int list. !i:num. !j:num. !x:int.
      !dp:(int list)list.
        LongestCommonSubsequence_fillRow
          i j x (CONS y ys) dp =
        let previousRow =
          LongestCommonSubsequence_getRow (i - 1) dp in
        let currentRow =
          LongestCommonSubsequence_getRow i dp in
        let newVal =
          if x = y then
            LongestCommonSubsequence_getInt (j - 1) previousRow + &1
          else
            intMax
              (LongestCommonSubsequence_getInt j previousRow)
              (LongestCommonSubsequence_getInt (j - 1) currentRow) in
        let updatedRow =
          LongestCommonSubsequence_setInt j newVal currentRow in
        let updatedDp =
          LongestCommonSubsequence_setRow i updatedRow dp in
        LongestCommonSubsequence_fillRow
          i (SUC j) x ys updatedDp)`;;

let LongestCommonSubsequence_fillRows =
  new_recursive_definition list_RECURSION
    `(!i:num. !b:int list. !dp:(int list)list.
        LongestCommonSubsequence_fillRows i [] b dp = dp) /\
     (!x:int. !xs:int list. !i:num. !b:int list.
      !dp:(int list)list.
        LongestCommonSubsequence_fillRows
          i (CONS x xs) b dp =
        let updatedDp =
          LongestCommonSubsequence_fillRow i 1 x b dp in
        LongestCommonSubsequence_fillRows
          (SUC i) xs b updatedDp)`;;

let LongestCommonSubsequence_precond = new_definition
  `LongestCommonSubsequence_precond
      (a:int list) (b:int list) <=> T`;;

let LongestCommonSubsequence = new_definition
  `LongestCommonSubsequence (a:int list) (b:int list) =
     let initialRow =
       REPLICATE (LENGTH b + 1) (&0:int) in
     let initialDp =
       REPLICATE (LENGTH a + 1) initialRow in
     let finalDp =
       LongestCommonSubsequence_fillRows 1 a b initialDp in
     LongestCommonSubsequence_getInt
       (LENGTH b)
       (LongestCommonSubsequence_getRow (LENGTH a) finalDp)`;;

let LongestCommonSubsequence_subseqFold =
  new_recursive_definition list_RECURSION
    `(!acc:(int list)list.
        LongestCommonSubsequence_subseqFold [] acc = acc) /\
     (!x:int. !xs:int list. !acc:(int list)list.
        LongestCommonSubsequence_subseqFold (CONS x xs) acc =
        LongestCommonSubsequence_subseqFold
          xs
          (APPEND acc
            (MAP (\sub:int list. CONS x sub) acc)))`;;

let LongestCommonSubsequence_allSubseq = new_definition
  `LongestCommonSubsequence_allSubseq (arr:int list) =
     MAP REVERSE
       (LongestCommonSubsequence_subseqFold
         arr (CONS ([]:int list) []))`;;

let LongestCommonSubsequence_postcond = new_definition
  `LongestCommonSubsequence_postcond
      (a:int list) (b:int list) (result:int) <=>
     let subseqA =
       LongestCommonSubsequence_allSubseq a in
     let subseqB =
       LongestCommonSubsequence_allSubseq b in
     let commonSubseqLens =
       MAP
         (\sub:int list. &(LENGTH sub))
         (FILTER (\sub:int list. MEM sub subseqB) subseqA) in
     MEM result commonSubseqLens /\
     ALL (\k:int. k <= result) commonSubseqLens`;;

let LongestCommonSubsequence_spec_satisfied =
  `!a:int list. !b:int list.
     LongestCommonSubsequence_precond a b
     ==> LongestCommonSubsequence_postcond
           a b (LongestCommonSubsequence a b)`;;
