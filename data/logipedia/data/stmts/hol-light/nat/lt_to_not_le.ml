(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_le,
  catalog title "nat.lt_to_not_le": strict natural-number order excludes the
  reverse non-strict order. This file contains no proof.
*)

let statement =
  `!n m:num. n < m ==> ~(m <= n)`;;
