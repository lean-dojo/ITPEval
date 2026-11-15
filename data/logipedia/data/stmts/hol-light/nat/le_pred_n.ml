(*
  Statement-only formalization of Logipedia corpus artifact nat.le_pred_n,
  catalog title "nat.le_pred_n": the predecessor of every natural number is
  less than or equal to that number. This file contains no proof.
*)

let statement =
  `!n:num. PRE n <= n`;;
