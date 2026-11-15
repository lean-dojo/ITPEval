(*
  Statement-only formalization of VERINA corpus artifact verina_basic_41
  (verina__hol-light__verina_basic_41), catalog title
  "hasOnlyOneDistinctElement": an executable first-element scan decides
  whether every integer in a nonempty finite array is equal, together with
  its nonemptiness precondition and full Boolean correctness contract. This
  file contains no proof.
*)

let hasOnlyOneDistinctElement_getDefault = new_definition
  `hasOnlyOneDistinctElement_getDefault
      (a:int list) (index:num) =
     if index < LENGTH a then EL index a else (&0:int)`;;

let hasOnlyOneDistinctElement_precond = new_definition
  `hasOnlyOneDistinctElement_precond (a:int list) <=>
     LENGTH a > 0`;;

let hasOnlyOneDistinctElement_loop =
  new_recursive_definition list_RECURSION
    `(hasOnlyOneDistinctElement_loop
        (first:int) ([]:int list) = T) /\
     (!first:int. !x:int. !xs:int list.
        hasOnlyOneDistinctElement_loop first (CONS x xs) =
        if x = first
        then hasOnlyOneDistinctElement_loop first xs
        else F)`;;

let hasOnlyOneDistinctElement =
  new_recursive_definition list_RECURSION
    `(hasOnlyOneDistinctElement ([]:int list) = T) /\
     (!x:int. !xs:int list.
        hasOnlyOneDistinctElement (CONS x xs) =
        hasOnlyOneDistinctElement_loop x xs)`;;

let hasOnlyOneDistinctElement_pairwise =
  new_recursive_definition list_RECURSION
    `(hasOnlyOneDistinctElement_pairwise ([]:int list) <=> T) /\
     (!x:int. !xs:int list.
        hasOnlyOneDistinctElement_pairwise (CONS x xs) <=>
        ALL (\y:int. x = y) xs /\
        hasOnlyOneDistinctElement_pairwise xs)`;;

let hasOnlyOneDistinctElement_anyDifferent =
  new_recursive_definition list_RECURSION
    `(hasOnlyOneDistinctElement_anyDifferent
        (first:int) ([]:int list) = F) /\
     (!first:int. !x:int. !xs:int list.
        hasOnlyOneDistinctElement_anyDifferent
          first (CONS x xs) =
        if ~(x = first)
        then T
        else hasOnlyOneDistinctElement_anyDifferent first xs)`;;

let hasOnlyOneDistinctElement_postcond = new_definition
  `hasOnlyOneDistinctElement_postcond
      (a:int list) (result:bool) <=>
     (result ==> hasOnlyOneDistinctElement_pairwise a) /\
     (~result
      ==> hasOnlyOneDistinctElement_anyDifferent
            (hasOnlyOneDistinctElement_getDefault a 0) a)`;;

let hasOnlyOneDistinctElement_spec_satisfied =
  `!a:int list.
     hasOnlyOneDistinctElement_precond a
     ==> hasOnlyOneDistinctElement_postcond
           a (hasOnlyOneDistinctElement a)`;;
