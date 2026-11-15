(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.Not_ind, catalog title "connectives.Not_ind": for propositions
  A and Q, a rule deriving Q from any map from A to the distinguished False
  proposition, together with the distinguished Not A proposition, entails Q.
  This file contains no proof.
*)

new_constant
  ("logipedia_connectives_false", `:bool`);;

new_constant
  ("logipedia_connectives_not", `:bool -> bool`);;

let statement =
  `!A Q:bool.
     (((A ==> (logipedia_connectives_false:bool)) ==> Q)
      ==> (logipedia_connectives_not:bool->bool) A
      ==> Q)`;;
