(*
  Statement-only formalization of Logipedia corpus artifact logic.trans_eq,
  catalog title "logic.trans_eq": equality is transitive for any three
  elements of an arbitrary type. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!x y z:A.
     logipedia_logic_eq x y
     ==> logipedia_logic_eq y z
     ==> logipedia_logic_eq x z`;;
