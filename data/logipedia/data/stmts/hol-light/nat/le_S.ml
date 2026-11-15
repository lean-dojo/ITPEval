(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S,
  catalog title "nat.le_S": natural-number order is preserved when the upper
  bound is replaced by its successor. This file contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> n <= SUC m`;;
