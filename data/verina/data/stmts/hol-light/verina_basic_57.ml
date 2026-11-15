(*
  Statement-only formalization of VERINA corpus artifact verina_basic_57
  (verina__hol-light__verina_basic_57), catalog title "CountLessThan": an
  executable indexed scan counts the integers in an array that are strictly
  below a threshold, together with its total precondition and
  truncated-subtraction correctness contract. This file contains no proof.
*)

let CountLessThan_precond = new_definition
  `CountLessThan_precond
      (numbers:int list) (threshold:int) <=> T`;;

let countLessThan_getDefault = new_definition
  `countLessThan_getDefault (numbers:int list) (i:num) =
     if i < LENGTH numbers then EL i numbers else (&0:int)`;;

let countLessThan_loopFuel =
  new_recursive_definition num_RECURSION
    `(!numbers:int list. !threshold:int. !i:num. !acc:num.
        countLessThan_loopFuel
          0 numbers threshold i acc = acc) /\
     (!fuel:num. !numbers:int list. !threshold:int.
      !i:num. !acc:num.
        countLessThan_loopFuel
          (SUC fuel) numbers threshold i acc =
        if i < LENGTH numbers then
          countLessThan_loopFuel
            fuel numbers threshold (i + 1)
            (if countLessThan_getDefault numbers i < threshold
             then acc + 1
             else acc)
        else
          acc)`;;

let countLessThan = new_definition
  `countLessThan (numbers:int list) (threshold:int) =
     countLessThan_loopFuel
       (SUC (LENGTH numbers)) numbers threshold 0 0`;;

let CountLessThan = new_definition
  `CountLessThan (numbers:int list) (threshold:int) =
     countLessThan numbers threshold`;;

let countLessThan_foldl =
  new_recursive_definition list_RECURSION
    `(!threshold:int. !acc:num.
        countLessThan_foldl
          ([]:int list) threshold acc = acc) /\
     (!n:int. !rest:int list. !threshold:int. !acc:num.
        countLessThan_foldl
          (CONS n rest) threshold acc =
        countLessThan_foldl
          rest threshold
          (if n < threshold then acc + 1 else acc))`;;

let CountLessThan_postcond = new_definition
  `CountLessThan_postcond
      (numbers:int list) (threshold:int) (result:num) <=>
     result - countLessThan_foldl numbers threshold 0 = 0 /\
     countLessThan_foldl numbers threshold 0 - result = 0`;;

let CountLessThan_spec_satisfied =
  `!numbers:int list. !threshold:int.
     CountLessThan_precond numbers threshold
     ==> CountLessThan_postcond
           numbers threshold
           (CountLessThan numbers threshold)`;;
