(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus, catalog title "nat.le_plus_to_minus": for natural
  numbers n, m, and p, if n is at most p plus m, then the truncated difference
  n minus m is at most p. This file contains no proof.
*)

let statement =
  `!n m p:num. n <= p + m ==> n - m <= p`;;
