(*
  Statement-only formalization of Logipedia corpus artifact exp.axiom_exp,
  catalog title "exp.axiom_exp": for all natural numbers n and m, the source
  equality relation identifies exp n m with the natural-type filter applied
  to exp_body n at m. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_exp_exp", `:num -> num -> num`);;

new_constant
  ("logipedia_exp_exp_body", `:num -> num -> num`);;

let statement =
  `!n m:num.
     logipedia_connectives_equal
       (logipedia_exp_exp n m)
       (logipedia_nat_filter_nat_type (logipedia_exp_exp_body n) m)`;;
