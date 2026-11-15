(*
  Statement-only formalization of VERINA corpus artifact verina_basic_103,
  catalog title "UpdateElements": an executable integer-array update,
  represented by a list, increments index 4 by 3 and sets index 7 to 516,
  together with its length and unchanged-elements correctness contract. This
  file contains no proof.
*)

let UpdateElements_precond = new_definition
  `UpdateElements_precond (a:int list) <=>
     8 <= LENGTH a`;;

let UpdateElements_updateAt =
  new_recursive_definition list_RECURSION
    `(!n:num. !v:int.
        UpdateElements_updateAt ([]:int list) n v = []) /\
     (!x:int. !xs:int list. !n:num. !v:int.
        UpdateElements_updateAt (CONS x xs) n v =
        if n = 0 then CONS v xs
        else CONS x (UpdateElements_updateAt xs (PRE n) v))`;;

let UpdateElements = new_definition
  `UpdateElements (a:int list) =
     let a1 =
       UpdateElements_updateAt a 4 (EL 4 a + &3) in
     UpdateElements_updateAt a1 7 (&516)`;;

let UpdateElements_postcond = new_definition
  `UpdateElements_postcond (a:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     EL 4 result = EL 4 a + &3 /\
     EL 7 result = &516 /\
     (!i:num.
        i < LENGTH a
        ==> ~(i = 4)
        ==> ~(i = 7)
        ==> EL i result = EL i a)`;;

let UpdateElements_spec_satisfied =
  `!a:int list.
     UpdateElements_precond a
     ==> UpdateElements_postcond a (UpdateElements a)`;;
