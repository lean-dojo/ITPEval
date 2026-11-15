(*
  Statement-only formalization of VERINA corpus artifact verina_basic_35
  (verina__hol-light__verina_basic_35), catalog title "MoveZeroesToEnd": an
  executable stable partition moves all zeroes in an integer array to the end,
  with the permutation and exact first-zero prefix/suffix correctness contract.
  This file contains no proof.
*)

let MoveZeroesToEnd_precond = new_definition
  `MoveZeroesToEnd_precond (arr:int list) <=> T`;;

let MoveZeroesToEnd = new_definition
  `MoveZeroesToEnd (arr:int list) =
     APPEND
       (FILTER (\x:int. ~(x = (&0:int))) arr)
       (FILTER (\x:int. x = (&0:int)) arr)`;;

let MoveZeroesToEnd_idxOf =
  new_recursive_definition list_RECURSION
    `(MoveZeroesToEnd_idxOf (value:int) [] = 0) /\
     (!x:int. !xs:int list. !value:int.
        MoveZeroesToEnd_idxOf value (CONS x xs) =
        if x = value then 0
        else SUC (MoveZeroesToEnd_idxOf value xs))`;;

let MoveZeroesToEnd_take =
  new_recursive_definition list_RECURSION
    `(!n:num.
        MoveZeroesToEnd_take n ([]:int list) = []) /\
     (!x:int. !xs:int list. !n:num.
        MoveZeroesToEnd_take n (CONS x xs) =
        if n = 0 then []
        else CONS x (MoveZeroesToEnd_take (PRE n) xs))`;;

let MoveZeroesToEnd_drop =
  new_recursive_definition list_RECURSION
    `(!n:num.
        MoveZeroesToEnd_drop n ([]:int list) = []) /\
     (!x:int. !xs:int list. !n:num.
        MoveZeroesToEnd_drop n (CONS x xs) =
        if n = 0 then CONS x xs
        else MoveZeroesToEnd_drop (PRE n) xs)`;;

let MoveZeroesToEnd_count = new_definition
  `MoveZeroesToEnd_count (value:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = value) xs)`;;

let MoveZeroesToEnd_isPerm = new_definition
  `MoveZeroesToEnd_isPerm (xs:int list) (ys:int list) <=>
     (!value:int.
        MoveZeroesToEnd_count value xs =
        MoveZeroesToEnd_count value ys)`;;

let MoveZeroesToEnd_postcond = new_definition
  `MoveZeroesToEnd_postcond
      (arr:int list) (result:int list) <=>
     let firstResZeroIdx =
       MoveZeroesToEnd_idxOf (&0:int) result in
     MoveZeroesToEnd_isPerm result arr /\
     MoveZeroesToEnd_take firstResZeroIdx result =
       FILTER (\x:int. ~(x = (&0:int))) arr /\
     MoveZeroesToEnd_drop firstResZeroIdx result =
       FILTER (\x:int. x = (&0:int)) arr`;;

let MoveZeroesToEnd_spec_satisfied =
  `!arr:int list.
     MoveZeroesToEnd_precond arr
     ==> MoveZeroesToEnd_postcond
           arr (MoveZeroesToEnd arr)`;;
