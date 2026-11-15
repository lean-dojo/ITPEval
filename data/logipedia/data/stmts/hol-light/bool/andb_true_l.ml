(*
  Statement-only formalization of Logipedia corpus artifact bool.andb_true_l,
  catalog title "bool.andb_true_l": if a Boolean conjunction is true, then
  its left operand is true. This file contains no proof.
*)

let logipedia_bool_andb = new_definition
  `logipedia_bool_andb (b1:bool) (b2:bool) =
     if b1 then b2 else F`;;

let statement =
  `!b1 b2:bool.
     logipedia_bool_andb b1 b2 = T
     ==>
     b1 = T`;;
