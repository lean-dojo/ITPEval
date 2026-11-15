(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_81,
  catalog title "uniqueSorted": an executable first-occurrence duplicate
  removal followed by insertion sort returns a nondecreasing permutation of
  the duplicate-free integer input. This file contains no proof.
*)

let uniqueSorted_precond = new_definition
  `uniqueSorted_precond (arr:int list) <=> T`;;

let uniqueSorted_insert =
  new_recursive_definition list_RECURSION
    `(uniqueSorted_insert (x:int) ([]:int list) = CONS x []) /\
     (!head:int. !tail:int list. !x:int.
        uniqueSorted_insert x (CONS head tail) =
        if x <= head
        then CONS x (CONS head tail)
        else CONS head (uniqueSorted_insert x tail))`;;

let uniqueSorted_insertionSort =
  new_recursive_definition list_RECURSION
    `(uniqueSorted_insertionSort ([]:int list) = []) /\
     (!head:int. !tail:int list.
        uniqueSorted_insertionSort (CONS head tail) =
        uniqueSorted_insert
          head (uniqueSorted_insertionSort tail))`;;

let uniqueSorted_removeDupsAux =
  new_recursive_definition list_RECURSION
    `(!seen:int list. !acc:int list.
        uniqueSorted_removeDupsAux
          ([]:int list) seen acc =
        REVERSE acc) /\
     (!head:int. !tail:int list. !seen:int list. !acc:int list.
        uniqueSorted_removeDupsAux
          (CONS head tail) seen acc =
        if MEM head seen then
          uniqueSorted_removeDupsAux tail seen acc
        else
          uniqueSorted_removeDupsAux
            tail (CONS head seen) (CONS head acc))`;;

let uniqueSorted_removeDups = new_definition
  `uniqueSorted_removeDups (arr:int list) =
     uniqueSorted_removeDupsAux arr [] []`;;

let uniqueSorted = new_definition
  `uniqueSorted (arr:int list) =
     uniqueSorted_insertionSort
       (uniqueSorted_removeDups arr)`;;

let uniqueSorted_count = new_definition
  `uniqueSorted_count (value:int) (xs:int list) =
     LENGTH (FILTER (\x:int. x = value) xs)`;;

let uniqueSorted_isPerm = new_definition
  `uniqueSorted_isPerm
      (xs:int list) (ys:int list) <=>
     !value:int.
       uniqueSorted_count value xs =
       uniqueSorted_count value ys`;;

let uniqueSorted_postcond = new_definition
  `uniqueSorted_postcond
      (arr:int list) (result:int list) <=>
     uniqueSorted_isPerm
       (uniqueSorted_removeDups arr) result /\
     PAIRWISE (\x y:int. x <= y) result`;;

let uniqueSorted_spec_satisfied =
  `!arr:int list.
     uniqueSorted_precond arr
     ==> uniqueSorted_postcond
           arr (uniqueSorted arr)`;;
