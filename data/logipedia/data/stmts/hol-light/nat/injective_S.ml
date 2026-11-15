(*
  Statement-only formalization of Logipedia corpus artifact nat.injective_S,
  catalog title "nat.injective_S": the successor function on natural numbers
  is injective. This file contains no proof.
*)

let statement =
  `!x y:num. SUC x = SUC y ==> x = y`;;
