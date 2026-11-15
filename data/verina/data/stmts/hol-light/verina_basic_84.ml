(*
  Statement-only formalization of VERINA corpus artifact verina_basic_84
  (verina__hol-light__verina_basic_84), catalog title "replace": an executable
  indexed traversal replaces every integer array entry greater than a threshold
  with -1 and leaves every other entry unchanged, together with its total
  precondition and length-and-pointwise correctness contract. This file
  contains no proof.
*)

let replace_precond = new_definition
  `replace_precond (arr:int list) (k:int) <=> T`;;

let replace_getDefault = new_definition
  `replace_getDefault (arr:int list) (i:num) =
     if i < LENGTH arr then EL i arr else (&0:int)`;;

let replace_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        replace_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        replace_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (replace_setAt xs (PRE i) value))`;;

let replace_loopFuel =
  new_recursive_definition num_RECURSION
    `(!oldArr:int list. !k:int. !i:num. !acc:int list.
        replace_loopFuel 0 oldArr k i acc = acc) /\
     (!fuel:num. !oldArr:int list. !k:int. !i:num. !acc:int list.
        replace_loopFuel (SUC fuel) oldArr k i acc =
        if i < LENGTH oldArr then
          if replace_getDefault oldArr i > k then
            replace_loopFuel fuel oldArr k (i + 1)
              (replace_setAt acc i (-- &1:int))
          else
            replace_loopFuel fuel oldArr k (i + 1) acc
        else
          acc)`;;

let replace_loop = new_definition
  `replace_loop
      (oldArr:int list) (k:int) (i:num) (acc:int list) =
     replace_loopFuel (LENGTH oldArr - i) oldArr k i acc`;;

let replace = new_definition
  `replace (arr:int list) (k:int) =
     replace_loop arr k 0 arr`;;

let replace_postcond = new_definition
  `replace_postcond
      (arr:int list) (k:int) (result:int list) <=>
     LENGTH result = LENGTH arr /\
     (!i:num.
        i < LENGTH arr
        ==> (EL i arr > k ==> EL i result = (-- &1:int))) /\
     (!i:num.
        i < LENGTH arr
        ==> (EL i arr <= k ==> EL i result = EL i arr))`;;

let replace_spec_satisfied =
  `!arr:int list. !k:int.
     replace_precond arr k
     ==> replace_postcond arr k (replace arr k)`;;
