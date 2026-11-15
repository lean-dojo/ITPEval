(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_S_to_lt,
  catalog title "nat.lt_S_to_lt": if the successor of a natural number is
  strictly less than another natural number, then the first natural number is
  strictly less than the second. This file contains no proof.
*)

let statement =
  `!n m:num. SUC n < m ==> n < m`;;
