(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_plus,
  catalog title "nat.axiom_plus": for every natural number n, the source
  equality relation identifies plus n with the natural-type filter applied
  to plus_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_plus n)
       (logipedia_nat_filter_nat_type logipedia_nat_plus_body n)`;;
