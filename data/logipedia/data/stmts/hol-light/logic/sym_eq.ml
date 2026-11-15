(*
  Statement-only formalization of Logipedia corpus artifact logic.sym_eq,
  catalog title "logic.sym_eq": equality is symmetric for any two elements
  of an arbitrary type. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!x y:A.
     logipedia_logic_eq x y
     ==> logipedia_logic_eq y x`;;
