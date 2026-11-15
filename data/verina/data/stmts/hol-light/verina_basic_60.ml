(*
  Statement-only formalization of VERINA corpus artifact verina_basic_60
  (verina__hol-light__verina_basic_60), catalog title "FindEvenNumbers": an
  executable left-to-right array scan returns exactly the even integers in
  their original order, together with its total precondition and
  all-elements, subsequence, and cardinality correctness contract. This file
  contains no proof.
*)

let isEven = new_definition
  `isEven (n:int) <=>
     n rem (&2:int) = (&0:int)`;;

let FindEvenNumbers_precond = new_definition
  `FindEvenNumbers_precond (arr:int list) <=> T`;;

let FindEvenNumbers_loop =
  new_recursive_definition list_RECURSION
    `(!acc:int list.
        FindEvenNumbers_loop ([]:int list) acc = acc) /\
     (!x:int. !xs:int list. !acc:int list.
        FindEvenNumbers_loop (CONS x xs) acc =
        FindEvenNumbers_loop xs
          (if isEven x then APPEND acc [x] else acc))`;;

let FindEvenNumbers = new_definition
  `FindEvenNumbers (arr:int list) =
     FindEvenNumbers_loop arr []`;;

let FindEvenNumbers_sublist =
  new_recursive_definition list_RECURSION
    `(!result:int list.
        FindEvenNumbers_sublist result [] <=>
        result = []) /\
     (!x:int. !xs:int list. !result:int list.
        FindEvenNumbers_sublist result (CONS x xs) <=>
        FindEvenNumbers_sublist result xs \/
        (?rest:int list.
           result = CONS x rest /\
           FindEvenNumbers_sublist rest xs))`;;

let FindEvenNumbers_countEven =
  new_recursive_definition list_RECURSION
    `(FindEvenNumbers_countEven ([]:int list) = 0) /\
     (!x:int. !xs:int list.
        FindEvenNumbers_countEven (CONS x xs) =
        if isEven x
        then SUC (FindEvenNumbers_countEven xs)
        else FindEvenNumbers_countEven xs)`;;

let FindEvenNumbers_postcond = new_definition
  `FindEvenNumbers_postcond
      (arr:int list) (result:int list) <=>
     ALL isEven result /\
     FindEvenNumbers_sublist result arr /\
     LENGTH result = FindEvenNumbers_countEven arr`;;

let FindEvenNumbers_spec_satisfied =
  `!arr:int list.
     FindEvenNumbers_precond arr
     ==> FindEvenNumbers_postcond
           arr (FindEvenNumbers arr)`;;
