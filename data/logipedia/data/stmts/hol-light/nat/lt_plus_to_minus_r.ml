(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_plus_to_minus_r, catalog title "nat.lt_plus_to_minus_r": for natural
  numbers a, b, and c, if a plus b is strictly less than c, then a is
  strictly less than the truncated natural difference c minus b. This file
  contains no proof.
*)

let statement =
  `!a b c:num. a + b < c ==> a < c - b`;;
