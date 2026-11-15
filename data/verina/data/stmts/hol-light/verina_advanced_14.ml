(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_14,
  catalog title "ifPowerOfFour": an executable natural-number recursion tests
  powers of four by repeated exact division, together with its total
  precondition and power-of-four postcondition. This file contains no proof.
*)

let ifPowerOfFour_precond = new_definition
  `ifPowerOfFour_precond (n:num) <=> T`;;

let ifPowerOfFour_helper = define
  `ifPowerOfFour_helper (n:num) =
     if n = 0 then F
     else if n = 1 then T
     else if n MOD 4 = 0
     then ifPowerOfFour_helper (n DIV 4)
     else F`;;

let ifPowerOfFour = new_definition
  `ifPowerOfFour (n:num) = ifPowerOfFour_helper n`;;

let ifPowerOfFour_postcond = new_definition
  `ifPowerOfFour_postcond (n:num) (result:bool) <=>
     (result <=> ?m:num. n = 4 EXP m)`;;

let ifPowerOfFour_spec_satisfied =
  `!n:num.
     ifPowerOfFour_precond n
     ==> ifPowerOfFour_postcond n (ifPowerOfFour n)`;;
