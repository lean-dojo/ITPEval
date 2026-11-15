(*
  Statement-only formalization of VERINA corpus artifact verina_basic_45
  (verina__hol-light__verina_basic_45), catalog title "findProduct": exact
  left-to-right scans of an integer list locate its first even and first odd
  elements, whose product is returned under the stated existence precondition
  and option-matched correctness contract. This file contains no proof.
*)

let findProduct_isEven = new_definition
  `findProduct_isEven (n:int) <=>
     n rem (&2:int) = (&0:int)`;;

let findProduct_isOdd = new_definition
  `findProduct_isOdd (n:int) <=>
     ~(n rem (&2:int) = (&0:int))`;;

let findProduct_findEvenIndex =
  new_recursive_definition list_RECURSION
    `(!i:num.
        findProduct_findEvenIndex ([]:int list) i =
        (NONE:num option)) /\
     (!x:int. !xs:int list. !i:num.
        findProduct_findEvenIndex (CONS x xs) i =
        if findProduct_isEven x then SOME i
        else findProduct_findEvenIndex xs (SUC i))`;;

let findProduct_findOddIndex =
  new_recursive_definition list_RECURSION
    `(!i:num.
        findProduct_findOddIndex ([]:int list) i =
        (NONE:num option)) /\
     (!x:int. !xs:int list. !i:num.
        findProduct_findOddIndex (CONS x xs) i =
        if findProduct_isOdd x then SOME i
        else findProduct_findOddIndex xs (SUC i))`;;

let findProduct_optionValue =
  new_recursive_definition option_RECURSION
    `(findProduct_optionValue (NONE:num option) = 0) /\
     (!i:num. findProduct_optionValue (SOME i) = i)`;;

let firstEvenOddIndices = new_definition
  `firstEvenOddIndices (lst:int list) =
     let evenIndex = findProduct_findEvenIndex lst 0 in
     let oddIndex = findProduct_findOddIndex lst 0 in
     if evenIndex = NONE then (NONE:(num#num) option)
     else if oddIndex = NONE then NONE
     else
       SOME
         (findProduct_optionValue evenIndex,
          findProduct_optionValue oddIndex)`;;

let findProduct_precond = new_definition
  `findProduct_precond (lst:int list) <=>
     LENGTH lst > 1 /\
     (?x:int. MEM x lst /\ findProduct_isEven x) /\
     (?x:int. MEM x lst /\ findProduct_isOdd x)`;;

let findProduct_by_indices =
  new_recursive_definition option_RECURSION
    `(!lst:int list.
        findProduct_by_indices
          (NONE:(num#num) option) lst = (&0:int)) /\
     (!indices:num#num. !lst:int list.
        findProduct_by_indices (SOME indices) lst =
        EL (FST indices) lst * EL (SND indices) lst)`;;

let findProduct = new_definition
  `findProduct (lst:int list) =
     findProduct_by_indices (firstEvenOddIndices lst) lst`;;

let findProduct_postcond_by_indices =
  new_recursive_definition option_RECURSION
    `(!lst:int list. !result:int.
        findProduct_postcond_by_indices
          (NONE:(num#num) option) lst result <=> T) /\
     (!indices:num#num. !lst:int list. !result:int.
        findProduct_postcond_by_indices
          (SOME indices) lst result <=>
        result = EL (FST indices) lst * EL (SND indices) lst)`;;

let findProduct_postcond = new_definition
  `findProduct_postcond (lst:int list) (result:int) <=>
     findProduct_postcond_by_indices
       (firstEvenOddIndices lst) lst result`;;

let findProduct_spec_satisfied =
  `!lst:int list.
     findProduct_precond lst
     ==> findProduct_postcond lst (findProduct lst)`;;
