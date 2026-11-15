(*
  Statement-only formalization of VERINA corpus artifact verina_basic_95
  (verina__hol-light__verina_basic_95), catalog title "swap": an executable
  two-update computation exchanges the entries at two valid nonnegative
  indices of an integer array, preserving its length and every other entry,
  together with its exact correctness contract. This file contains no proof.
*)

let swap_intToNat = new_definition
  `swap_intToNat (z:int) =
     if z < (&0:int) then 0 else num_of_int z`;;

let swap_getDefault = new_definition
  `swap_getDefault (arr:int list) (index:num) =
     if index < LENGTH arr then EL index arr else (&0:int)`;;

let swap_setAt =
  new_recursive_definition list_RECURSION
    `(!index:num. !value:int.
        swap_setAt ([]:int list) index value = []) /\
     (!x:int. !xs:int list. !index:num. !value:int.
        swap_setAt (CONS x xs) index value =
        if index = 0 then CONS value xs
        else CONS x (swap_setAt xs (PRE index) value))`;;

let swap_precond = new_definition
  `swap_precond (arr:int list) (i:int) (j:int) <=>
     (&0:int) <= i /\
     (&0:int) <= j /\
     swap_intToNat i < LENGTH arr /\
     swap_intToNat j < LENGTH arr`;;

let swap = new_definition
  `swap (arr:int list) (i:int) (j:int) =
     let i_nat = swap_intToNat i in
     let j_nat = swap_intToNat j in
     let arr1 =
       swap_setAt arr i_nat (swap_getDefault arr j_nat) in
     swap_setAt arr1 j_nat (swap_getDefault arr i_nat)`;;

let swap_postcond = new_definition
  `swap_postcond
      (arr:int list) (i:int) (j:int) (result:int list) <=>
     LENGTH result = LENGTH arr /\
     swap_getDefault result (swap_intToNat i) =
       swap_getDefault arr (swap_intToNat j) /\
     swap_getDefault result (swap_intToNat j) =
       swap_getDefault arr (swap_intToNat i) /\
     (!k:num.
        k < LENGTH arr
        ==> ~(k = swap_intToNat i)
        ==> ~(k = swap_intToNat j)
        ==> swap_getDefault result k = swap_getDefault arr k)`;;

let swap_spec_satisfied =
  `!arr:int list. !i:int. !j:int.
     swap_precond arr i j
     ==> swap_postcond arr i j (swap arr i j)`;;
