(*
  Statement-only formalization of VERINA corpus artifact verina_basic_62
  (verina__hol-light__verina_basic_62), catalog title "Find": an executable
  left-to-right scan of an integer array returns the first index containing
  the key, or -1 when the key is absent, together with its total precondition
  and exact first-occurrence correctness contract. This file contains no
  proof.
*)

let find_precond_def = new_definition
  `Find_precond (a:int list) (key:int) <=> T`;;

let find_search_def =
  new_recursive_definition list_RECURSION
    `(!key:int. !index:num.
        Find_search ([]:int list) key index = (-- &1:int)) /\
     (!x:int. !xs:int list. !key:int. !index:num.
        Find_search (CONS x xs) key index =
        if x = key then
          &index
        else
          Find_search xs key (SUC index))`;;

let find_def = new_definition
  `Find (a:int list) (key:int) =
     Find_search a key 0`;;

let find_int_to_nat_def = new_definition
  `Find_intToNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let find_get_default_def = new_definition
  `Find_getDefault (a:int list) (index:num) =
     if index < LENGTH a then EL index a else (&0:int)`;;

let find_postcond_def = new_definition
  `Find_postcond (a:int list) (key:int) (result:int) <=>
     (result = -- &1 \/
      (result >= &0 /\ result < &(LENGTH a))) /\
     (~(result = -- &1)
      ==> Find_getDefault a (Find_intToNat result) = key /\
          (!i:num.
             i < Find_intToNat result
             ==> ~(Find_getDefault a i = key))) /\
     (result = -- &1
      ==> (!i:num.
             i < LENGTH a
             ==> ~(Find_getDefault a i = key)))`;;

let find_spec_satisfied_statement =
  `!a:int list. !key:int.
     Find_precond a key
     ==> Find_postcond a key (Find a key)`;;
