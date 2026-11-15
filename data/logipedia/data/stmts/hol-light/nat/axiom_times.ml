(*
  Statement-only formalization of Logipedia corpus artifact nat.axiom_times,
  catalog title "nat.axiom_times": for every natural number n, the source
  equality relation identifies times n with the natural-type filter applied
  to times_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_nat_times", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_times n)
       (logipedia_nat_filter_nat_type logipedia_nat_times_body n)`;;
