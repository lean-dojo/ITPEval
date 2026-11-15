(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_559. This file
  contains no proof.
*)

let statement = `!x y:num.
  x MOD 3 = 2 /\
  y MOD 5 = 4 /\
  x MOD 10 = y MOD 10
  ==> 14 <= x`;;
