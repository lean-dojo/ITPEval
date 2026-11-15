(*
  Statement-only formalization of Logipedia corpus artifact nat.le_to_not_lt,
  catalog title "nat.le_to_not_lt": for natural numbers n and m, n <= m
  implies that m is not less than n. This file contains no proof.
*)

let statement =
  `!n m:num. n <= m ==> ~(m < n)`;;
