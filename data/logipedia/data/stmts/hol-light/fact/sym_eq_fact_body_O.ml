(*
  Statement-only formalization of Logipedia corpus artifact
  fact.sym_eq_fact_body_O, catalog title "fact.sym_eq_fact_body_O": Leibniz
  equality transports every predicate holding of one to fact_body at zero.
  This file contains no proof.
*)

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!P:num->bool.
     P 1
     ==>
     P (logipedia_fact_fact_body 0)`;;
