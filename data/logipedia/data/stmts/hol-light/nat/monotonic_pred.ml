(*
  Statement-only formalization of Logipedia corpus artifact nat.monotonic_pred,
  catalog title "nat.monotonic_pred": the predecessor operation on natural
  numbers is monotone with respect to the natural-number order. This file
  contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> PRE n <= PRE m`;;
