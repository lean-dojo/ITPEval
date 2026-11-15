(*
  Statement-only formalization of Logipedia corpus artifact
  fact.eq_fact_body_S, catalog title "fact.eq_fact_body_S": for every natural
  number n, Leibniz equality transports every predicate holding of fact_body
  at the successor of n to fact n multiplied by that successor. This file
  contains no proof.
*)

new_constant
  ("logipedia_fact_fact", `:num -> num`);;

new_constant
  ("logipedia_fact_fact_body", `:num -> num`);;

let statement =
  `!n:num.
   !P:num->bool.
     P (logipedia_fact_fact_body (SUC n))
     ==>
     P (logipedia_fact_fact n * SUC n)`;;
