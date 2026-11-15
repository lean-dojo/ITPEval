(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.or_intror, catalog title "connectives.or_intror": for
  propositions A and B, assumption B entails the distinguished disjunction
  proposition connectives.Or A B. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_or", `:bool -> bool -> bool`);;

let statement =
  `!A B:bool.
     B ==> (logipedia_connectives_or:bool->bool->bool) A B`;;
