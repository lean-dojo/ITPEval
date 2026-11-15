(*
  Statement-only formalization of Logipedia corpus artifact nat.le_ind,
  catalog title "nat.le_ind": induction over natural numbers at or above a
  fixed lower bound. This file contains no proof.
*)

let statement =
  `!n:num. !Q:num->bool.
     Q n ==>
     (!m:num. n <= m ==> Q m ==> Q (SUC m)) ==>
     (!m:num. n <= m ==> Q m)`;;
