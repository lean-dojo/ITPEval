(*
  Statement-only formalization of Logipedia corpus artifact nat.times_n_Sm,
  catalog title "nat.times_n_Sm": for all natural numbers n and m, n plus n
  multiplied by m equals n multiplied by the successor of m. This file
  contains no proof.
*)

let statement =
  `!n m:num. n + n * m = n * SUC m`;;
