(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_not_zero, catalog title "nat.lt_to_not_zero": a natural number
  greater than another natural number is nonzero. This file contains no proof.
*)

let statement =
  `!n m:num. n < m ==> ~(m = 0)`;;
