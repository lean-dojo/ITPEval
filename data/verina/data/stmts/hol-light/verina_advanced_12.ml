(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_12,
  catalog title "firstDuplicate": an executable left-to-right list scan returns
  the first integer encountered for a second time, with its total precondition
  and occurrence-index postcondition. This file contains no proof.
*)

let firstDuplicate_precond = new_definition
  `firstDuplicate_precond (lst:int list) <=> T`;;

let firstDuplicate_helper =
  new_recursive_definition list_RECURSION
    `(firstDuplicate_helper (seen:int list) [] = (NONE:int option)) /\
     (!h:int. !t:int list. !seen:int list.
        firstDuplicate_helper seen (CONS h t) =
        if MEM h seen
        then SOME h
        else firstDuplicate_helper (CONS h seen) t)`;;

let firstDuplicate = new_definition
  `firstDuplicate (lst:int list) = firstDuplicate_helper [] lst`;;

let firstDuplicate_idxOf =
  new_recursive_definition list_RECURSION
    `(firstDuplicate_idxOf (v:int) [] = 0) /\
     (!h:int. !t:int list. !v:int.
        firstDuplicate_idxOf v (CONS h t) =
        if h = v then 0 else SUC (firstDuplicate_idxOf v t))`;;

let firstDuplicate_drop =
  new_recursive_definition num_RECURSION
    `(!lst:int list. firstDuplicate_drop 0 lst = lst) /\
     (!n:num. !lst:int list.
        firstDuplicate_drop (SUC n) lst =
        if lst = [] then [] else firstDuplicate_drop n (TL lst))`;;

let secondOccIdx = new_definition
  `secondOccIdx (lst:int list) (v:int) =
     let first = firstDuplicate_idxOf v lst in
     first + 1 +
     firstDuplicate_idxOf v (firstDuplicate_drop (first + 1) lst)`;;

let firstDuplicate_count = new_definition
  `firstDuplicate_count (lst:int list) (v:int) =
     LENGTH (FILTER (\x:int. x = v) lst)`;;

let firstDuplicate_nodup =
  new_recursive_definition list_RECURSION
    `(firstDuplicate_nodup ([]:int list) <=> T) /\
     (!h:int. !t:int list.
        firstDuplicate_nodup (CONS h t) <=>
        ~MEM h t /\ firstDuplicate_nodup t)`;;

let firstDuplicate_postcond = new_definition
  `firstDuplicate_postcond
      (lst:int list) (result:int option) <=>
     (result = NONE /\ firstDuplicate_nodup lst) \/
     (?x:int.
        result = SOME x /\
        firstDuplicate_count lst x > 1 /\
        ALL
          (\y:int.
             firstDuplicate_count lst y = 1 \/
             secondOccIdx lst x <= secondOccIdx lst y)
          lst)`;;

let firstDuplicate_spec_satisfied =
  `!lst:int list.
     firstDuplicate_precond lst
     ==> firstDuplicate_postcond lst (firstDuplicate lst)`;;
