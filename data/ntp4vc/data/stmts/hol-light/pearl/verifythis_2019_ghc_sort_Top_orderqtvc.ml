(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_orderqtvc: the verification condition
  for orienting a strictly increasing or nonincreasing integer list so that
  the result is nondecreasing and a permutation of the input. This file
  contains no proof.
*)

let ghc_order_strictly_increasing =
  new_recursive_definition list_RECURSION
   `(ghc_order_strictly_increasing ([]:int list) = T) /\
    (!x:int.
     !xs:int list.
       ghc_order_strictly_increasing (CONS x xs) =
       if xs = [] then
         T
       else
         x < HD xs /\ ghc_order_strictly_increasing xs)`;;

let ghc_order_nondecreasing =
  new_recursive_definition list_RECURSION
   `(ghc_order_nondecreasing ([]:int list) = T) /\
    (!x:int.
     !xs:int list.
       ghc_order_nondecreasing (CONS x xs) =
       if xs = [] then
         T
       else
         x <= HD xs /\ ghc_order_nondecreasing xs)`;;

let ghc_order_nonincreasing =
  new_recursive_definition list_RECURSION
   `(ghc_order_nonincreasing ([]:int list) = T) /\
    (!x:int.
     !xs:int list.
       ghc_order_nonincreasing (CONS x xs) =
       if xs = [] then
         T
       else
         HD xs <= x /\ ghc_order_nonincreasing xs)`;;

let ghc_order_count =
  new_recursive_definition list_RECURSION
   `(!value:int.
       ghc_order_count value ([]:int list) = (&0:int)) /\
    (!value head:int.
     !tail:int list.
       ghc_order_count value (CONS head tail) =
       (if head = value then (&1:int) else (&0:int)) +
       ghc_order_count value tail)`;;

let ghc_order_permutation = new_definition
 `ghc_order_permutation (left:int list) (right:int list) <=>
    !value:int.
      ghc_order_count value left = ghc_order_count value right`;;

let ghc_order_result = new_definition
 `ghc_order_result (l:int list) =
    if l = [] then
      l
    else if TL l = [] then
      l
    else if HD l < HD (TL l) then
      l
    else
      REVERSE l`;;

let statement =
 `!l:int list.
    ghc_order_strictly_increasing l \/ ghc_order_nonincreasing l
    ==>
    (if l = [] then T else if TL l = [] then T else T) /\
    (!result:int list.
       result = ghc_order_result l
       ==>
       ghc_order_nondecreasing result /\
       ghc_order_permutation l result)`;;
