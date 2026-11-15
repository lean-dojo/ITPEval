(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_S, catalog title "fact.axiom_fact_body_S": for every
  natural number n, the source equality relation identifies fact_body at the
  successor of n with fact n multiplied by that successor. This file contains
  no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_fact_fact", `:num -> num`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_fact_fact_body (SUC n))
       (logipedia_fact_fact n * SUC n)`;;
