(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_to_le,
  catalog title "nat.le_plus_to_le": for natural numbers, adding the same
  number on the left preserves enough order to cancel it from an inequality.
  This file contains no proof.
*)

let statement =
  `!a n m:num. a + n <= a + m ==> n <= m`;;
