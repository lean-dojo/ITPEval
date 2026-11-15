(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_35,
  catalog title "majorityElement": an executable integer-list scan returns
  the unique value occurring strictly more than half the time, under the
  nonempty-majority precondition and with its occurrence-count postcondition.
  This file contains no proof.
*)

let majorityElement_count =
  new_recursive_definition list_RECURSION
    `(majorityElement_count (value:int) [] = 0) /\
     (!x:int. !xs:int list. !value:int.
        majorityElement_count value (CONS x xs) =
        if x = value
        then SUC (majorityElement_count value xs)
        else majorityElement_count value xs)`;;

let majorityElement_precond = new_definition
  `majorityElement_precond (nums:int list) <=>
     0 < LENGTH nums /\
     (?x:int.
        MEM x nums /\
        majorityElement_count x nums > LENGTH nums DIV 2)`;;

let majorityElement_scan =
  new_recursive_definition list_RECURSION
    `(!whole:int list.
        majorityElement_scan whole [] = (&0:int)) /\
     (!x:int. !xs:int list. !whole:int list.
        majorityElement_scan whole (CONS x xs) =
        if majorityElement_count x whole > LENGTH whole DIV 2
        then x
        else majorityElement_scan whole xs)`;;

let majorityElement = new_definition
  `majorityElement (nums:int list) =
     majorityElement_scan nums nums`;;

let majorityElement_postcond = new_definition
  `majorityElement_postcond (nums:int list) (result:int) <=>
     majorityElement_count result nums > LENGTH nums DIV 2 /\
     (!x:int.
        MEM x nums /\ ~(x = result)
        ==> majorityElement_count x nums <= LENGTH nums DIV 2)`;;

let majorityElement_spec_satisfied =
  `!nums:int list.
     majorityElement_precond nums
     ==> majorityElement_postcond nums (majorityElement nums)`;;
