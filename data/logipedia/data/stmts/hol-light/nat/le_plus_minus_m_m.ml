(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_minus_m_m, catalog title "nat.le_plus_minus_m_m": every natural
  number n is at most the sum of its truncated difference from m and m.
  This file contains no proof.
*)

let statement =
  `!n m:num. n <= (n - m) + m`;;
