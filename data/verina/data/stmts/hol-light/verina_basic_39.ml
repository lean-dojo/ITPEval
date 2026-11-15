(*
  Statement-only formalization of VERINA corpus artifact verina_basic_39
  (verina__hol-light__verina_basic_39), catalog title "rotateRight": an
  executable rotation maps each integer-list position to the index obtained
  by subtracting a natural offset modulo the list length, together with its
  total precondition and pointwise optional-index correctness contract. This
  file contains no proof.
*)

let rotateRight_precond = new_definition
  `rotateRight_precond (l:int list) (n:num) <=> T`;;

let rotateRight_range =
  new_recursive_definition num_RECURSION
    `(rotateRight_range 0 = []) /\
     (!k:num.
        rotateRight_range (SUC k) =
        APPEND (rotateRight_range k) (CONS k []))`;;

let rotateRight_intToNat = new_definition
  `rotateRight_intToNat (z:int) =
     if z < &0 then 0 else num_of_int z`;;

let rotateRight_index = new_definition
  `rotateRight_index (i:num) (n:num) (len:num) =
     rotateRight_intToNat
       (((&i:int) - (&n:int) + (&len:int)) rem (&len:int))`;;

let rotateRight_headDefault = new_definition
  `rotateRight_headDefault (l:int list) =
     if l = [] then (&0:int) else HD l`;;

let rotateRight_getDefault = new_definition
  `rotateRight_getDefault (l:int list) (index:num) =
     if index < LENGTH l then EL index l
     else rotateRight_headDefault l`;;

let rotateRight_getOption = new_definition
  `rotateRight_getOption (l:int list) (index:num) =
     if index < LENGTH l then SOME (EL index l)
     else (NONE:int option)`;;

let rotateRight = new_definition
  `rotateRight (l:int list) (n:num) =
     let len = LENGTH l in
     if len = 0 then l
     else
       MAP
         (\i:num.
            rotateRight_getDefault l
              (rotateRight_index i n len))
         (rotateRight_range len)`;;

let rotateRight_postcond = new_definition
  `rotateRight_postcond
      (l:int list) (n:num) (result:int list) <=>
     LENGTH result = LENGTH l /\
     (!i:num.
        i < LENGTH l
        ==> rotateRight_getOption result i =
            rotateRight_getOption l
              (rotateRight_index i n (LENGTH l)))`;;

let rotateRight_spec_satisfied =
  `!l:int list. !n:num.
     rotateRight_precond l n
     ==> rotateRight_postcond l n (rotateRight l n)`;;
