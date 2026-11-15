(*
  Statement-only formalization of Logipedia corpus artifact connectives.nmk,
  catalog title "connectives.nmk": for every proposition A, a function from A
  to the distinguished False proposition entails the distinguished Not A
  proposition. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_false", `:bool`);;

new_constant
  ("logipedia_connectives_not", `:bool -> bool`);;

let statement =
  `!A:bool.
     (A ==> (logipedia_connectives_false:bool))
     ==> (logipedia_connectives_not:bool->bool) A`;;
