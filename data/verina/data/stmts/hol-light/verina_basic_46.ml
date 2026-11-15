(*
  Statement-only formalization of VERINA corpus artifact verina_basic_46
  (verina__hol-light__verina_basic_46), catalog title "lastPosition": an
  executable left-to-right scan of a nondecreasing integer array returns the
  last index containing a target element, or -1 when absent, together with its
  full last-occurrence correctness contract. This file contains no proof.
*)

let lastPosition_pairwiseLe =
  new_recursive_definition list_RECURSION
    `(lastPosition_pairwiseLe ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        lastPosition_pairwiseLe (CONS x xs) <=>
        ALL (\y:int. x <= y) xs /\
        lastPosition_pairwiseLe xs)`;;

let lastPosition_precond = new_definition
  `lastPosition_precond (arr:int list) (elem:int) <=>
     lastPosition_pairwiseLe arr`;;

let lastPosition_loop =
  new_recursive_definition list_RECURSION
    `(!elem:int. !i:num. !pos:int.
        lastPosition_loop ([]:int list) elem i pos = pos) /\
     (!x:int. !xs:int list. !elem:int. !i:num. !pos:int.
        lastPosition_loop (CONS x xs) elem i pos =
        if x = elem then
          lastPosition_loop xs elem (SUC i) (&i:int)
        else
          lastPosition_loop xs elem (SUC i) pos)`;;

let lastPosition = new_definition
  `lastPosition (arr:int list) (elem:int) =
     lastPosition_loop arr elem 0 (-- &1:int)`;;

let lastPosition_toNat = new_definition
  `lastPosition_toNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let lastPosition_drop =
  new_recursive_definition num_RECURSION
    `(!xs:int list.
        lastPosition_drop 0 xs = xs) /\
     (!n:num. !xs:int list.
        lastPosition_drop (SUC n) xs =
        if xs = [] then []
        else lastPosition_drop n (TL xs))`;;

let lastPosition_postcond = new_definition
  `lastPosition_postcond
      (arr:int list) (elem:int) (result:int) <=>
     (result = -- &1 \/ result >= &0) /\
     (result >= &0
      ==> lastPosition_toNat result < LENGTH arr /\
          EL (lastPosition_toNat result) arr = elem /\
          ALL
            (\x:int. ~(x = elem))
            (lastPosition_drop
              (lastPosition_toNat result + 1) arr)) /\
     (result = -- &1
      ==> ALL (\x:int. ~(x = elem)) arr)`;;

let lastPosition_spec_satisfied =
  `!arr:int list. !elem:int.
     lastPosition_precond arr elem
     ==> lastPosition_postcond
           arr elem (lastPosition arr elem)`;;
