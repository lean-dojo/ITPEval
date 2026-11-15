(*
  Statement-only formalization of Logipedia corpus artifact nat.not_eq_S,
  catalog title "nat.not_eq_S": unequal natural numbers have unequal
  successors. This file contains no proof.
*)

let statement =
  `!n m:num. ~(n = m) ==> ~(SUC n = SUC m)`;;
