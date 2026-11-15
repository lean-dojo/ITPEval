(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus_r, catalog title "nat.le_plus_to_minus_r": for natural
  numbers a, b, and c, if a plus b is at most c, then a is at most the
  truncated natural difference c minus b. This file contains no proof.
*)

let statement =
  `!a b c:num. a + b <= c ==> a <= c - b`;;
