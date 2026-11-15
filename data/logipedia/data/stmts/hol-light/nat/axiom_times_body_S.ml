(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_times_body_S, catalog title "nat.axiom_times_body_S": for every
  natural number n, the source equality relation identifies times_body at the
  successor of n with the function mapping m to plus m (times n m). This file
  contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_times_body (SUC n))
       (\m:num. logipedia_nat_plus m (logipedia_nat_times n m))`;;
