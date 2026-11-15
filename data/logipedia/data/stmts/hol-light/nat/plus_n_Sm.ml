(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_n_Sm,
  catalog title "nat.plus_n_Sm": for all natural numbers n and m, the
  successor of n + m equals n plus the successor of m. This file contains no
  proof.
*)

let statement =
  `!n m:num. SUC (n + m) = n + SUC m`;;
