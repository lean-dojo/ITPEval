(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_minus,
  catalog title "nat.axiom_minus": for every natural number n, the source
  equality relation identifies minus n with the natural-type filter applied
  to minus_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_minus n)
       (logipedia_nat_filter_nat_type logipedia_nat_minus_body n)`;;
