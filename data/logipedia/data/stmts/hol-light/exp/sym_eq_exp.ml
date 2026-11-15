(*
  Statement-only formalization of Logipedia corpus artifact exp.sym_eq_exp,
  catalog title "exp.sym_eq_exp": for all natural numbers n and m, Leibniz
  equality transports every predicate holding of the natural-type filter
  applied to exp_body n at m to exp n m. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_exp_exp", `:num -> num -> num`);;

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n m:num.
   !P:num->bool.
     P (logipedia_nat_filter_nat_type
          (logipedia_exp_exp_body n) m)
     ==>
     P (logipedia_exp_exp n m)`;;
