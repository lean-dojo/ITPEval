(*
  Statement-only formalization of Logipedia corpus artifact nat.ltn_to_ltO,
  catalog title "nat.ltn_to_ltO": if one natural number is strictly less than
  another, then the latter is strictly positive. This file contains no proof.
*)

let statement =
  `!n m:num. n < m ==> 0 < m`;;
