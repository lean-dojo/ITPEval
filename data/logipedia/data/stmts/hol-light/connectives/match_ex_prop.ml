(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_ex_prop, catalog title "connectives.match_ex_prop": for
  any type, predicate P, and proposition return_, a rule deriving return_
  from P x for every x, together with the distinguished existential
  proposition connectives.ex P, entails return_. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_ex", `:('a -> bool) -> bool`);;

let statement =
  `!P:'a->bool.
   !return_:bool.
     (!x:'a. P x ==> return_)
     ==> (logipedia_connectives_ex:('a->bool)->bool) P
     ==> return_`;;
