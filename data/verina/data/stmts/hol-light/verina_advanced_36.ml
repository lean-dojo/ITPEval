(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_36,
  catalog title "majorityElement": an executable Boyer-Moore-style scan on
  natural-number lists returns a value occurring strictly more than half the
  time under the nonempty-majority precondition. This file contains no proof.
*)

let majorityElement_countOccurrences =
  new_recursive_definition list_RECURSION
    `(majorityElement_countOccurrences
        (target:num) ([]:num list) = 0) /\
     (!y:num. !ys:num list. !target:num.
        majorityElement_countOccurrences
          target (CONS y ys) =
        if y = target
        then SUC (majorityElement_countOccurrences target ys)
        else majorityElement_countOccurrences target ys)`;;

let majorityElement_precond = new_definition
  `majorityElement_precond (xs:num list) <=>
     0 < LENGTH xs /\
     EX
       (\x:num.
          majorityElement_countOccurrences x xs >
          LENGTH xs DIV 2)
       xs`;;

let majorityElement_optionValue =
  new_recursive_definition option_RECURSION
    `(majorityElement_optionValue (NONE:num option) = 0) /\
     (!c:num.
        majorityElement_optionValue (SOME c) = c)`;;

let majorityElement_findCandidate =
  new_recursive_definition list_RECURSION
    `(!candidate:num option. !count:num.
        majorityElement_findCandidate
          ([]:num list) candidate count =
        if candidate = NONE
        then 0
        else majorityElement_optionValue candidate) /\
     (!x:num. !xs:num list.
      !candidate:num option. !count:num.
        majorityElement_findCandidate
          (CONS x xs) candidate count =
        if candidate = NONE then
          majorityElement_findCandidate xs (SOME x) 1
        else
          let c = majorityElement_optionValue candidate in
          if x = c then
            majorityElement_findCandidate
              xs (SOME c) (count + 1)
          else if count = 0 then
            majorityElement_findCandidate xs (SOME x) 1
          else
            majorityElement_findCandidate
              xs (SOME c) (count - 1))`;;

let majorityElement = new_definition
  `majorityElement (xs:num list) =
     majorityElement_findCandidate xs NONE 0`;;

let majorityElement_postcond = new_definition
  `majorityElement_postcond
      (xs:num list) (result:num) <=>
     majorityElement_countOccurrences result xs >
     LENGTH xs DIV 2`;;

let majorityElement_spec_satisfied =
  `!xs:num list.
     majorityElement_precond xs
     ==> majorityElement_postcond
           xs (majorityElement xs)`;;
