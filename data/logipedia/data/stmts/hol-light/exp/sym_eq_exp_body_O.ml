(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_O, catalog title "exp.sym_eq_exp_body_O": for every
  natural number n, Leibniz equality transports every predicate holding of
  one to exp_body n at zero. This file contains no proof.
*)

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:num->bool.
     P 1
     ==>
     P (logipedia_exp_exp_body n 0)`;;
