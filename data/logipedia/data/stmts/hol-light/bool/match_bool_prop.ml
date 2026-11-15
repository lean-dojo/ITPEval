(*
  Statement-only formalization of Logipedia corpus artifact
  bool.match_bool_prop, catalog title "bool.match_bool_prop": every predicate
  on Booleans that holds for both true and false holds for every Boolean.
  This file contains no proof.
*)

let statement =
  `!return_:bool->bool.
     return_ T
     ==>
     return_ F
     ==>
     !z:bool. return_ z`;;
