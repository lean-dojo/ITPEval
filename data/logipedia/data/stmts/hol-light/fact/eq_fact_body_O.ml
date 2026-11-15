(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_O, catalog title "fact.eq_fact_body_O": Leibniz equality
  transports every predicate holding of fact_body at zero to one. This file
  contains no proof.
*)

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!P:num->bool.
     P (logipedia_fact_fact_body 0)
     ==>
     P 1`;;
