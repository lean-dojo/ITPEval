(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_56,
  catalog title "moveZeroes": an executable stable partition moves all zeroes
  in an integer list to the end while preserving the relative order of the
  nonzero elements, together with its full correctness contract. This file
  contains no proof.
*)

let moveZeroes_precond = new_definition
  `moveZeroes_precond (xs:int list) <=> T`;;

let moveZeroes = new_definition
  `moveZeroes (xs:int list) =
     APPEND
       (FILTER (\x:int. ~(x = (&0:int))) xs)
       (FILTER (\x:int. x = (&0:int)) xs)`;;

let countVal =
  new_recursive_definition list_RECURSION
    `(!val:int.
        countVal val ([]:int list) = 0) /\
     (!x:int. !xs:int list. !val:int.
        countVal val (CONS x xs) =
        let rest = countVal val xs in
        if x = val then rest + 1 else rest)`;;

let isSubsequence =
  new_recursive_definition list_RECURSION
    `(!xs:int list.
        isSubsequence xs ([]:int list) <=> xs = []) /\
     (!y:int. !ys:int list. !xs:int list.
        isSubsequence xs (CONS y ys) <=>
        if xs = [] then T
        else if HD xs = y
        then isSubsequence (TL xs) ys
        else isSubsequence xs ys)`;;

let moveZeroes_dropWhileNonzero =
  new_recursive_definition list_RECURSION
    `(moveZeroes_dropWhileNonzero ([]:int list) = []) /\
     (!x:int. !xs:int list.
        moveZeroes_dropWhileNonzero (CONS x xs) =
        if ~(x = (&0:int))
        then moveZeroes_dropWhileNonzero xs
        else CONS x xs)`;;

let moveZeroes_postcond = new_definition
  `moveZeroes_postcond (xs:int list) (result:int list) <=>
     isSubsequence
       (FILTER (\x:int. ~(x = (&0:int))) xs)
       result /\
     ALL
       (\x:int. x = (&0:int))
       (moveZeroes_dropWhileNonzero result) /\
     countVal (&0:int) xs = countVal (&0:int) result /\
     LENGTH xs = LENGTH result`;;

let moveZeroes_spec_satisfied =
  `!xs:int list.
     moveZeroes_precond xs
     ==> moveZeroes_postcond xs (moveZeroes xs)`;;
