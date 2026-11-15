(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_times_r, catalog title "nat.monotonic_le_times_r":
  left multiplication by a fixed natural number is monotone with respect to
  the natural-number order. This file contains no proof.
*)

let statement =
  `!n x y:num. x <= y ==> n * x <= n * y`;;
