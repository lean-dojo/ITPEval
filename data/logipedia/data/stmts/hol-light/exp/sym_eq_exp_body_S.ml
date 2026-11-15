(*
  Statement-only formalization of Logipedia corpus artifact
  exp.sym_eq_exp_body_S, catalog title "exp.sym_eq_exp_body_S": for all
  natural numbers n and m, Leibniz equality transports every predicate
  holding of exp n m multiplied by n to exp_body n at the successor of m.
  This file contains no proof.
*)

new_constant
  ("logipedia_exp_exp", `:num -> num -> num`);;

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n m:num.
   !P:num->bool.
     P (logipedia_exp_exp n m * n)
     ==>
     P (logipedia_exp_exp_body n (SUC m))`;;
