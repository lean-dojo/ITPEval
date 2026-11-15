(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_plus_l, catalog title "nat.monotonic_lt_plus_l":
  adding a fixed natural number on the right is strictly monotone with respect
  to the natural-number order. This file contains no proof.
*)

let statement =
  `!n x y:num. x < y ==> x + n < y + n`;;
