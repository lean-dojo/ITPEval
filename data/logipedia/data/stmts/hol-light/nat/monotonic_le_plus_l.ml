(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_plus_l, catalog title "nat.monotonic_le_plus_l":
  adding a fixed natural number on the right is monotone with respect to the
  natural-number order. This file contains no proof.
*)

let statement =
  `!m x y:num. x <= y ==> x + m <= y + m`;;
