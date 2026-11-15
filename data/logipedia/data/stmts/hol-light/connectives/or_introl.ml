(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_introl, catalog title "connectives.or_introl": for
  propositions A and B, assumption A entails the distinguished disjunction
  proposition connectives.Or A B. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_or", `:bool -> bool -> bool`);;

let statement =
  `!A B:bool.
     A ==> (logipedia_connectives_or:bool->bool->bool) A B`;;
