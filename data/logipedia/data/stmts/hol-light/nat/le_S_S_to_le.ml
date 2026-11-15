(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S_S_to_le,
  catalog title "nat.le_S_S_to_le": natural-number order between successors
  implies the corresponding order between their predecessors. This file
  contains no proof.
*)

let statement =
  `!n m:num. SUC n <= SUC m ==> n <= m`;;
