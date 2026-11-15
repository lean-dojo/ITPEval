(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_le_r, catalog title "nat.le_plus_to_le_r": for natural
  numbers, canceling the same right addend from an inequality preserves
  order. This file contains no proof.
*)

let statement =
  `!a n m:num. n + a <= m + a ==> n <= m`;;
