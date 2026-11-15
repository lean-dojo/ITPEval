(*
  Statement-only formalization of Logipedia corpus artifact
  fact.sym_eq_fact_body_S, catalog title "fact.sym_eq_fact_body_S": for every
  natural number n, Leibniz equality transports every predicate holding of
  fact n multiplied by the successor of n to fact_body at that successor.
  This file contains no proof.
*)

new_constant
  ("logipedia_fact_fact", `:num -> num`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!n:num.
   !P:num->bool.
     P (logipedia_fact_fact n * SUC n)
     ==>
     P (logipedia_fact_fact_body (SUC n))`;;
