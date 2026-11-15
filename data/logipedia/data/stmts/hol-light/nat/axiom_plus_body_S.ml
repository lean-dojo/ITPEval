(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_plus_body_S, catalog title "nat.axiom_plus_body_S": for every
  natural number n, the source equality relation identifies plus_body at the
  successor of n with the function mapping m to the successor of plus n m.
  This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_plus_body (SUC n))
       (\m:num. SUC (logipedia_nat_plus n m))`;;
