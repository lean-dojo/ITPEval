(*
  Statement-only formalization of Logipedia corpus artifact div_mod.eq_div_O,
  catalog title "div_mod.eq_div_O": if one natural number is strictly less
  than another, its natural quotient by the larger number is zero. This file
  contains no proof.
*)

let statement =
  `!n m:num.
     n < m
     ==>
     n DIV m = 0`;;
