(*
  Statement-only formalization of Logipedia corpus artifact connectives.conj,
  catalog title "connectives.conj": for propositions A and B, assumptions A
  and B entail the distinguished conjunction proposition connectives.And A B.
  This file contains no proof.
*)

new_constant
  ("logipedia_connectives_and", `:bool -> bool -> bool`);;

let statement =
  `!A B:bool.
     A ==> B ==> (logipedia_connectives_and:bool->bool->bool) A B`;;
