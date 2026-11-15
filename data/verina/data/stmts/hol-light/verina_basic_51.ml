(*
  Statement-only formalization of VERINA corpus artifact verina_basic_51
  (verina__hol-light__verina_basic_51), catalog title "BinarySearch": an
  executable lower-bound binary search on a nondecreasing integer array,
  together with its insertion-index correctness contract. This file contains
  no proof.
*)

let binarySearch_getDefault = new_definition
  `binarySearch_getDefault (a:int list) (i:num) =
     if i < LENGTH a then EL i a else (&0:int)`;;

let BinarySearch_precond = new_definition
  `BinarySearch_precond (a:int list) (key:int) <=>
     PAIRWISE (\x y:int. x <= y) a`;;

let binarySearchLoopFuel =
  new_recursive_definition num_RECURSION
    `(!a:int list. !key:int. !lo:num. !hi:num.
        binarySearchLoopFuel 0 a key lo hi = lo) /\
     (!fuel:num. !a:int list. !key:int. !lo:num. !hi:num.
        binarySearchLoopFuel (SUC fuel) a key lo hi =
        if lo < hi then
          let mid = (lo + hi) DIV 2 in
          if binarySearch_getDefault a mid < key then
            binarySearchLoopFuel fuel a key (mid + 1) hi
          else
            binarySearchLoopFuel fuel a key lo mid
        else
          lo)`;;

let binarySearchLoop = new_definition
  `binarySearchLoop
      (a:int list) (key:int) (lo:num) (hi:num) =
     binarySearchLoopFuel (hi - lo) a key lo hi`;;

let BinarySearch = new_definition
  `BinarySearch (a:int list) (key:int) =
     binarySearchLoop a key 0 (LENGTH a)`;;

let BinarySearch_postcond = new_definition
  `BinarySearch_postcond
      (a:int list) (key:int) (result:num) <=>
     result <= LENGTH a /\
     (!i:num.
        i < result
        ==> binarySearch_getDefault a i < key) /\
     (!i:num.
        result <= i /\ i < LENGTH a
        ==> key <= binarySearch_getDefault a i)`;;

let BinarySearch_spec_satisfied =
  `!a:int list. !key:int.
     BinarySearch_precond a key
     ==> BinarySearch_postcond
           a key (BinarySearch a key)`;;
