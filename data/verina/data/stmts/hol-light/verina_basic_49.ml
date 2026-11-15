(*
  Statement-only formalization of VERINA corpus artifact verina_basic_49
  (verina__hol-light__verina_basic_49), catalog title "findFirstOdd": an
  executable left-to-right scan of a nonempty integer array returns the first
  odd element's natural-number index, or no index when every element is even,
  together with its exact first-occurrence correctness contract. This file
  contains no proof.
*)

let findFirstOdd_isOdd = new_definition
  `findFirstOdd_isOdd (x:int) <=>
     ~(x rem (&2:int) = (&0:int))`;;

let findFirstOdd_precond = new_definition
  `findFirstOdd_precond (a:int list) <=>
     LENGTH a > 0`;;

let findFirstOdd_scan =
  new_recursive_definition list_RECURSION
    `(!i:num.
        findFirstOdd_scan ([]:int list) i =
        (NONE:num option)) /\
     (!x:int. !xs:int list. !i:num.
        findFirstOdd_scan (CONS x xs) i =
        if findFirstOdd_isOdd x then
          SOME i
        else
          findFirstOdd_scan xs (SUC i))`;;

let findFirstOdd = new_definition
  `findFirstOdd (a:int list) =
     findFirstOdd_scan a 0`;;

let findFirstOdd_postcond = new_definition
  `findFirstOdd_postcond
      (a:int list) (result:num option) <=>
     (result = NONE /\
      (!i:num.
         i < LENGTH a
         ==> ~findFirstOdd_isOdd (EL i a))) \/
     (?idx:num.
        result = SOME idx /\
        idx < LENGTH a /\
        findFirstOdd_isOdd (EL idx a) /\
        (!j:num.
           j < idx
           ==> ~findFirstOdd_isOdd (EL j a)))`;;

let findFirstOdd_spec_satisfied =
  `!a:int list.
     findFirstOdd_precond a
     ==> findFirstOdd_postcond a (findFirstOdd a)`;;
