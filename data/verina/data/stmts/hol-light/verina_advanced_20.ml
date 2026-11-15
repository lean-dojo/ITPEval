(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_20,
  catalog title "isItEight": an executable integer test recognizes numbers
  divisible by eight or containing the decimal digit eight, together with its
  total correctness contract. This file contains no proof.
*)

let hasDigitEight = define
  `hasDigitEight (m:num) =
     if m = 0 then F
     else if m MOD 10 = 8 then T
     else hasDigitEight (m DIV 10)`;;

let isItEight_precond = new_definition
  `isItEight_precond (n:int) <=> T`;;

let isItEight = new_definition
  `isItEight (n:int) =
     let absN = num_of_int (abs n) in
     n rem &8 = &0 \/ hasDigitEight absN`;;

let isItEight_postcond = new_definition
  `isItEight_postcond (n:int) (result:bool) <=>
     let absN = num_of_int (abs n) in
     (n rem &8 = &0 \/
      ?i:num. (absN DIV (10 EXP i)) MOD 10 = 8) <=>
     result`;;

let isItEight_spec_satisfied =
  `!n:int.
     isItEight_precond n
     ==> isItEight_postcond n (isItEight n)`;;
