(*
  Statement-only formalization of Logipedia corpus artifact fact.axiom_fact,
  catalog title "fact.axiom_fact": for every natural number n, the source
  equality relation identifies fact n with the natural-type filter applied to
  fact_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_fact_fact", `:num -> num`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_fact_fact n)
       (logipedia_nat_filter_nat_type logipedia_fact_fact_body n)`;;
