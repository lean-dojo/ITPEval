(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_le,
  catalog title "nat.lt_to_le": strict order between two natural numbers
  implies the corresponding less-than-or-equal relation. This file contains
  no proof.
*)

let statement =
  `!x y:num. x < y ==> x <= y`;;
