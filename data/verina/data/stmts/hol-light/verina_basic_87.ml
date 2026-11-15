(*
  Statement-only formalization of VERINA corpus artifact verina_basic_87
  (verina__hol-light__verina_basic_87), catalog title "SelectionSort": an
  executable selection sort on an integer array, including defaulted indexing,
  guarded indexed updates, minimum-index scanning, and the outer traversal,
  with its total precondition and sorted-permutation correctness contract.
  This file contains no proof.
*)

let SelectionSort_getDefault = new_definition
  `SelectionSort_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let SelectionSort_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        SelectionSort_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        SelectionSort_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (SelectionSort_setAt xs (PRE i) value))`;;

let SelectionSort_precond = new_definition
  `SelectionSort_precond (a:int list) <=> T`;;

let findMinIndexInRangeFuel =
  new_recursive_definition num_RECURSION
    `(!arr:int list. !currIdx:num. !minIdx:num.
        findMinIndexInRangeFuel 0 arr currIdx minIdx = minIdx) /\
     (!fuel:num. !arr:int list. !currIdx:num. !minIdx:num.
        findMinIndexInRangeFuel
          (SUC fuel) arr currIdx minIdx =
        let nextMinIdx =
          if SelectionSort_getDefault arr currIdx <
             SelectionSort_getDefault arr minIdx
          then currIdx
          else minIdx in
        findMinIndexInRangeFuel
          fuel arr (currIdx + 1) nextMinIdx)`;;

let findMinIndexInRange = new_definition
  `findMinIndexInRange
      (arr:int list) (start:num) (finish:num) =
     findMinIndexInRangeFuel
       (finish - start) arr start start`;;

let swap = new_definition
  `swap (a:int list) (i:num) (j:num) =
     if i < LENGTH a /\ j < LENGTH a /\ ~(i = j) then
       let temp = SelectionSort_getDefault a i in
       let a' =
         SelectionSort_setAt
           a i (SelectionSort_getDefault a j) in
       SelectionSort_setAt a' j temp
     else
       a`;;

let SelectionSort_loop =
  new_recursive_definition num_RECURSION
    `(!finish:num. !i:num. !arr:int list.
        SelectionSort_loop 0 finish i arr = arr) /\
     (!fuel:num. !finish:num. !i:num. !arr:int list.
        SelectionSort_loop (SUC fuel) finish i arr =
        let minIdx =
          findMinIndexInRange arr i finish in
        let arr' = swap arr i minIdx in
        SelectionSort_loop fuel finish (i + 1) arr')`;;

let SelectionSort = new_definition
  `SelectionSort (a:int list) =
     SelectionSort_loop
       (LENGTH a) (LENGTH a) 0 a`;;

let SelectionSort_count = new_definition
  `SelectionSort_count (value:int) (a:int list) =
     LENGTH (FILTER (\x:int. x = value) a)`;;

let SelectionSort_isPerm = new_definition
  `SelectionSort_isPerm (xs:int list) (ys:int list) <=>
     !value:int.
       SelectionSort_count value xs =
       SelectionSort_count value ys`;;

let SelectionSort_postcond = new_definition
  `SelectionSort_postcond
      (a:int list) (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     SelectionSort_isPerm a result`;;

let SelectionSort_spec_satisfied =
  `!a:int list.
     SelectionSort_precond a
     ==> SelectionSort_postcond
           a (SelectionSort a)`;;
