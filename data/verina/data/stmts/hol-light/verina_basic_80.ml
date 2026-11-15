(*
  Statement-only formalization of VERINA corpus artifact verina_basic_80
  (verina__hol-light__verina_basic_80), catalog title "only_once": an
  executable left-to-right scan determines whether an integer key occurs
  exactly once in an array, with its total precondition and exact occurrence-
  count correctness contract. This file contains no proof.
*)

let only_once_precond = new_definition
  `only_once_precond (a:int list) (key:int) <=> T`;;

let only_once_loopFuel =
  new_recursive_definition num_RECURSION
    `(!a:'a list. !key:'a. !i:num. !keyCount:num.
        only_once_loopFuel 0 a key i keyCount =
        (keyCount = 1)) /\
     (!fuel:num. !a:'a list. !key:'a. !i:num. !keyCount:num.
        only_once_loopFuel (SUC fuel) a key i keyCount =
        if i < LENGTH a then
          let value = EL i a in
          let newCount =
            if value = key then keyCount + 1 else keyCount in
          only_once_loopFuel fuel a key (i + 1) newCount
        else
          keyCount = 1)`;;

let only_once_loop = new_definition
  `only_once_loop
      (a:'a list) (key:'a) (i:num) (keyCount:num) =
     only_once_loopFuel
       (LENGTH a - i) a key i keyCount`;;

let only_once = new_definition
  `only_once (a:int list) (key:int) =
     only_once_loop a key 0 0`;;

let count_occurrences_aux =
  new_recursive_definition list_RECURSION
    `(!key:'a. !count:num.
        count_occurrences_aux ([]:'a list) key count = count) /\
     (!x:'a. !xs:'a list. !key:'a. !count:num.
        count_occurrences_aux (CONS x xs) key count =
        count_occurrences_aux
          xs key (if x = key then count + 1 else count))`;;

let count_occurrences = new_definition
  `count_occurrences (a:'a list) (key:'a) =
     count_occurrences_aux a key 0`;;

let only_once_postcond = new_definition
  `only_once_postcond
      (a:int list) (key:int) (result:bool) <=>
     (count_occurrences a key = 1 ==> result) /\
     (~(count_occurrences a key = 1) ==> ~result)`;;

let only_once_spec_satisfied =
  `!a:int list. !key:int.
     only_once_precond a key
     ==> only_once_postcond a key (only_once a key)`;;
