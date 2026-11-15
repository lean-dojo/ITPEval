(*
  Statement-only formalization of Logipedia corpus artifact nat.S_pred,
  catalog title "nat.S_pred": every positive natural number is the successor
  of its predecessor. This file contains no proof.
*)

let statement =
  `!n:num. 0 < n ==> SUC (PRE n) = n`;;
