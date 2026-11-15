(*
  Statement-only formalization of Logipedia corpus artifact exp.eq_exp_body_O,
  catalog title "exp.eq_exp_body_O": for every natural number n, Leibniz
  equality transports every predicate holding of exp_body n at zero to one.
  This file contains no proof.
*)

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:num->bool.
     P (logipedia_exp_exp_body n 0)
     ==>
     P 1`;;
