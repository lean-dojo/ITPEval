(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_r, catalog title "nat.monotonic_le_plus_r":
  adding a fixed natural number on the left is monotone with respect to the
  natural-number order. This file contains no proof.
*)

let statement =
  `!n x y:num. x <= y ==> n + x <= n + y`;;
