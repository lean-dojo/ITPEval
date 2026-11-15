(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_r, catalog title "nat.monotonic_le_minus_r":
  for natural numbers p, q, and n, q <= p implies that subtracting p from n
  is at most subtracting q from n. This file contains no proof.
*)

let statement =
  `!p q n:num. q <= p ==> n - p <= n - q`;;
