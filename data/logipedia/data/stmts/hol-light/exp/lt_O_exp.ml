(*
  Statement-only formalization of Logipedia corpus artifact exp.lt_O_exp,
  catalog title "exp.lt_O_exp": for all natural numbers n and m, positivity
  of n implies positivity of n raised to the power m. This file contains no
  proof.
*)

let statement =
  `!n m:num.
     0 < n
     ==>
     0 < n EXP m`;;
