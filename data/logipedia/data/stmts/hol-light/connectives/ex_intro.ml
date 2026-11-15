(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.ex_intro, catalog title "connectives.ex_intro": for any type,
  predicate P, and element x, P x entails the distinguished existential
  proposition connectives.ex P. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_ex", `:('a -> bool) -> bool`);;

let statement =
  `!P:'a->bool.
   !x:'a.
     P x
     ==> (logipedia_connectives_ex:('a->bool)->bool) P`;;
