(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_not_le_S_S, catalog title "nat.not_le_to_not_le_S_S":
  failure of the natural-number order relation is preserved when both
  arguments are replaced by their successors. This file contains no proof.
*)

let statement =
  `!n m:num. ~(n <= m) ==> ~(SUC n <= SUC m)`;;
