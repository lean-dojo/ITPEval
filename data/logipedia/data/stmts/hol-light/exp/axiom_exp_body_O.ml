(*
  Statement-only formalization of Logipedia corpus artifact
  exp.axiom_exp_body_O, catalog title "exp.axiom_exp_body_O": for every
  natural number n, the source equality relation identifies exp_body n at
  zero with one. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_exp_exp_body n 0)
       1`;;
