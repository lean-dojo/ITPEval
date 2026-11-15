(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_l, catalog title "nat.monotonic_le_minus_l":
  for natural numbers p, q, and n, q <= p implies that truncated subtraction
  of n preserves this order. This file contains no proof.
*)

let statement =
  `!p q n:num. q <= p ==> q - n <= p - n`;;
