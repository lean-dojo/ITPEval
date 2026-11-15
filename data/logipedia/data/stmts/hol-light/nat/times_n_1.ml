(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_1,
  catalog title "nat.times_n_1": every natural number equals itself multiplied
  by the successor of zero (one). This file contains no proof.
*)

let statement =
  `!n:num. n = n * (SUC 0)`;;
