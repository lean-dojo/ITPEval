(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_And_prop, catalog title "connectives.match_And_prop": for
  propositions A, B, and return_, a rule deriving return_ from A and B,
  together with the distinguished conjunction proposition connectives.And A B,
  entails return_. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_and", `:bool -> bool -> bool`);;

let statement =
  `!A B return_:bool.
     (A ==> B ==> return_)
     ==> (logipedia_connectives_and:bool->bool->bool) A B
     ==> return_`;;
