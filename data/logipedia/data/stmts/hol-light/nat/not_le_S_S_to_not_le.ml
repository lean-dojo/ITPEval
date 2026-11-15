(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_S_S_to_not_le, catalog title "nat.not_le_S_S_to_not_le":
  failure of the natural-number order relation between two successors implies
  failure of the order relation between their predecessors. This file contains
  no proof.
*)

let statement =
  `!n m:num. ~(SUC n <= SUC m) ==> ~(n <= m)`;;
