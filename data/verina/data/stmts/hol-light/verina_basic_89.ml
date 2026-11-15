(*
  Statement-only formalization of VERINA corpus artifact verina_basic_89
  (verina__hol-light__verina_basic_89), catalog title "SetToSeq": an
  executable left-to-right deduplication of an integer list preserves exactly
  its elements and their first-occurrence order, with a unique output
  occurrence for each retained element. This file contains no proof.
*)

let SetToSeq_precond = new_definition
  `SetToSeq_precond (s:int list) <=> T`;;

let SetToSeq_foldl =
  new_recursive_definition list_RECURSION
    `(!acc:int list.
        SetToSeq_foldl ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int list.
        SetToSeq_foldl (CONS x xs) acc =
        SetToSeq_foldl xs
          (if MEM x acc then acc else APPEND acc [x]))`;;

let SetToSeq = new_definition
  `SetToSeq (s:int list) =
     SetToSeq_foldl s ([]:int list)`;;

let SetToSeq_count =
  new_recursive_definition list_RECURSION
    `(!a:int.
        SetToSeq_count ([]:int list) a = 0) /\
     (!x:int. !xs:int list. !a:int.
        SetToSeq_count (CONS x xs) a =
        if x = a then SUC (SetToSeq_count xs a)
        else SetToSeq_count xs a)`;;

let SetToSeq_idxOf =
  new_recursive_definition list_RECURSION
    `(!a:int.
        SetToSeq_idxOf ([]:int list) a = 0) /\
     (!x:int. !xs:int list. !a:int.
        SetToSeq_idxOf (CONS x xs) a =
        if x = a then 0
        else SUC (SetToSeq_idxOf xs a))`;;

let SetToSeq_postcond = new_definition
  `SetToSeq_postcond (s:int list) (result:int list) <=>
     ALL (\a:int. MEM a s) result /\
     ALL (\a:int. MEM a result) s /\
     ALL (\a:int. SetToSeq_count result a = 1) result /\
     PAIRWISE
       (\a b:int.
          SetToSeq_idxOf result a < SetToSeq_idxOf result b
          ==> SetToSeq_idxOf s a < SetToSeq_idxOf s b)
       result`;;

let SetToSeq_spec_satisfied =
  `!s:int list.
     SetToSeq_precond s
     ==> SetToSeq_postcond s (SetToSeq s)`;;
