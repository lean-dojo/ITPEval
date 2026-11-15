(*
  Statement-only formalization of Logipedia corpus artifact
  fact.axiom_fact_body_O, catalog title "fact.axiom_fact_body_O": the source
  equality relation identifies fact_body at zero with one. This file contains
  no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_fact_fact_body 0)
     1`;;
