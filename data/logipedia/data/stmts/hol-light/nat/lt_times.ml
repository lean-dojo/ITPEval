(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_times,
  catalog title "nat.lt_times": strict natural-number inequalities in both
  factors imply a strict inequality between their products. This file contains
  no proof.
*)

let statement =
  `!n m p q:num. n < m ==> p < q ==> n * p < m * q`;;
