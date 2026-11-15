(*
  Statement-only formalization of VERINA corpus artifact verina_basic_52
  (verina__hol-light__verina_basic_52), catalog title "BubbleSort": an
  executable bubble-sort traversal of an integer array, including defaulted
  indexing, indexed updates, swapping, and the inner and outer loops, with its
  total precondition and sorted-permutation correctness contract. This file
  contains no proof.
*)

let bubbleSort_getDefault = new_definition
  `bubbleSort_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let bubbleSort_setAt =
  new_recursive_definition list_RECURSION
    `(!i:num. !value:int.
        bubbleSort_setAt ([]:int list) i value = []) /\
     (!x:int. !xs:int list. !i:num. !value:int.
        bubbleSort_setAt (CONS x xs) i value =
        if i = 0 then CONS value xs
        else CONS x (bubbleSort_setAt xs (PRE i) value))`;;

let BubbleSort_precond = new_definition
  `BubbleSort_precond (a:int list) <=> T`;;

let swap = new_definition
  `swap (a:int list) (i:num) (j:num) =
     let temp = bubbleSort_getDefault a i in
     let a1 =
       bubbleSort_setAt a i (bubbleSort_getDefault a j) in
     bubbleSort_setAt a1 j temp`;;

let bubbleInnerFuel =
  new_recursive_definition num_RECURSION
    `(!j:num. !i:num. !a:int list.
        bubbleInnerFuel 0 j i a = a) /\
     (!fuel:num. !j:num. !i:num. !a:int list.
        bubbleInnerFuel (SUC fuel) j i a =
        if j < i then
          let a' =
            if bubbleSort_getDefault a j >
               bubbleSort_getDefault a (j + 1)
            then swap a j (j + 1)
            else a in
          bubbleInnerFuel fuel (j + 1) i a'
        else
          a)`;;

let bubbleInner = new_definition
  `bubbleInner (j:num) (i:num) (a:int list) =
     bubbleInnerFuel (i - j) j i a`;;

let bubbleOuter =
  new_recursive_definition num_RECURSION
    `(!a:int list.
        bubbleOuter 0 a = a) /\
     (!i:num. !a:int list.
        bubbleOuter (SUC i) a =
        let a' = bubbleInner 0 (SUC i) a in
        bubbleOuter i a')`;;

let BubbleSort = new_definition
  `BubbleSort (a:int list) =
     if LENGTH a = 0 then a
     else bubbleOuter (LENGTH a - 1) a`;;

let BubbleSort_count = new_definition
  `BubbleSort_count (value:int) (a:int list) =
     LENGTH (FILTER (\x:int. x = value) a)`;;

let BubbleSort_isPerm = new_definition
  `BubbleSort_isPerm (xs:int list) (ys:int list) <=>
     !value:int.
       BubbleSort_count value xs =
       BubbleSort_count value ys`;;

let BubbleSort_postcond = new_definition
  `BubbleSort_postcond
      (a:int list) (result:int list) <=>
     PAIRWISE (\x y:int. x <= y) result /\
     BubbleSort_isPerm result a`;;

let BubbleSort_spec_satisfied =
  `!a:int list.
     BubbleSort_precond a
     ==> BubbleSort_postcond a (BubbleSort a)`;;
