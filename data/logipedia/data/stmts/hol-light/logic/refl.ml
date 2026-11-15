(*
  Statement-only formalization of Logipedia corpus artifact logic.refl,
  catalog title "logic.refl": the polymorphic equality relation is reflexive
  for every element of every type. This file contains no proof.
*)

let logipedia_logic_eq = new_definition
  `logipedia_logic_eq (x:A) (y:A) <=> x = y`;;

let statement =
  `!x:A. logipedia_logic_eq x x`;;
