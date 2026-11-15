(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_eq,
  catalog title "nat.lt_to_not_eq": strict order between two natural numbers
  implies that the numbers are unequal. This file contains no proof.
*)

let statement =
  `!n m:num. n < m ==> ~(n = m)`;;
