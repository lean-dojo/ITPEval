(*
  Statement-only formalization of Logipedia corpus artifact fact.eq_fact,
  catalog title "fact.eq_fact": for every natural number n, Leibniz equality
  transports every predicate holding of fact n to the natural-type filter
  applied to fact_body at n. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_fact_fact", `:num -> num`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!n:num.
   !P:num->bool.
     P (logipedia_fact_fact n)
     ==>
     P (logipedia_nat_filter_nat_type logipedia_fact_fact_body n)`;;
