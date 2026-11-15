(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_lt_times_l, catalog title "nat.monotonic_lt_times_l":
  right multiplication by a positive natural number is strictly monotone with
  respect to the natural-number order. This file contains no proof.
*)

let statement =
  `!c x y:num. 0 < c ==> x < y ==> x * c < y * c`;;
