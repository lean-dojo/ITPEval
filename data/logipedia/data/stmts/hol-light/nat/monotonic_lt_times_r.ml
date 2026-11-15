(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_r, catalog title "nat.monotonic_lt_times_r":
  left multiplication by a positive natural number is strictly monotone with
  respect to the natural-number order. This file contains no proof.
*)

let statement =
  `!c x y:num. 0 < c ==> x < y ==> c * x < c * y`;;
