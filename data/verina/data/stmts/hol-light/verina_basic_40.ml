(*
  Statement-only formalization of VERINA corpus artifact verina_basic_40
  (verina__hol-light__verina_basic_40), catalog title "secondSmallest": an
  executable index-tracking scan returns the second-smallest distinct integer
  in a finite array, together with its distinctness precondition and full
  correctness contract. This file contains no proof.
*)

let secondSmallest_getDefault = new_definition
  `secondSmallest_getDefault (s:int list) (index:num) =
     if index < LENGTH s then EL index s else (&0:int)`;;

let secondSmallest_precond = new_definition
  `secondSmallest_precond (s:int list) <=>
     LENGTH s > 1 /\
     (?i:num. ?j:num.
        i < LENGTH s /\
        j < LENGTH s /\
        ~(secondSmallest_getDefault s i =
          secondSmallest_getDefault s j))`;;

let secondSmallest_optionValue =
  new_recursive_definition option_RECURSION
    `(secondSmallest_optionValue (NONE:num option) = 0) /\
     (!index:num.
        secondSmallest_optionValue (SOME index) = index)`;;

let secondSmallest_finish = new_definition
  `secondSmallest_finish
      (s:int list) (secondIdx:num option) =
     if secondIdx = NONE then (&0:int)
     else
       secondSmallest_getDefault s
         (secondSmallest_optionValue secondIdx)`;;

let secondSmallestAux_fuel =
  new_recursive_definition num_RECURSION
    `(!s:int list. !i:num. !minIdx:num. !secondIdx:num option.
        secondSmallestAux_fuel
          0 s i minIdx secondIdx =
        secondSmallest_finish s secondIdx) /\
     (!fuel:num. !s:int list. !i:num. !minIdx:num.
      !secondIdx:num option.
        secondSmallestAux_fuel
          (SUC fuel) s i minIdx secondIdx =
        if LENGTH s <= i then
          secondSmallest_finish s secondIdx
        else
          let x = secondSmallest_getDefault s i in
          let m = secondSmallest_getDefault s minIdx in
          if secondIdx = NONE then
            if x < m then
              secondSmallestAux_fuel
                fuel s (i + 1) i (SOME minIdx)
            else if x > m then
              secondSmallestAux_fuel
                fuel s (i + 1) minIdx (SOME i)
            else
              secondSmallestAux_fuel
                fuel s (i + 1) minIdx NONE
          else
            let si =
              secondSmallest_optionValue secondIdx in
            let smin =
              secondSmallest_getDefault s si in
            if x < m then
              secondSmallestAux_fuel
                fuel s (i + 1) i (SOME minIdx)
            else if x < smin /\ x > m then
              secondSmallestAux_fuel
                fuel s (i + 1) minIdx (SOME i)
            else
              secondSmallestAux_fuel
                fuel s (i + 1) minIdx (SOME si))`;;

let secondSmallestAux = new_definition
  `secondSmallestAux
      (s:int list) (i:num) (minIdx:num)
      (secondIdx:num option) =
     secondSmallestAux_fuel
       (LENGTH s - i) s i minIdx secondIdx`;;

let secondSmallest = new_definition
  `secondSmallest (s:int list) =
     secondSmallestAux s 1 0 NONE`;;

let secondSmallest_postcond = new_definition
  `secondSmallest_postcond
      (s:int list) (result:int) <=>
     (?i:num.
        i < LENGTH s /\
        secondSmallest_getDefault s i = result) /\
     (?j:num.
        j < LENGTH s /\
        secondSmallest_getDefault s j < result /\
        (!k:num.
           k < LENGTH s
           ==> ~(secondSmallest_getDefault s k =
                 secondSmallest_getDefault s j)
           ==> result <= secondSmallest_getDefault s k))`;;

let secondSmallest_spec_satisfied =
  `!s:int list.
     secondSmallest_precond s
     ==> secondSmallest_postcond s (secondSmallest s)`;;
