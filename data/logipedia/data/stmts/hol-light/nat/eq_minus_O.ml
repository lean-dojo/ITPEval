(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus_O,
  catalog title "nat.eq_minus_O": if one natural number is at most another,
  their truncated natural subtraction is zero. This file contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> n - m = 0`;;
