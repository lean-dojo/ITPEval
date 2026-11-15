(*
  Statement-only formalization of Logipedia corpus artifact nat.times_times,
  catalog title "nat.times_times": for all natural numbers x, y, and z,
  reordering the first two factors in the nested product x * (y * z) gives
  y * (x * z). This file contains no proof.
*)

let statement =
  `!x y z:num. x * (y * z) = y * (x * z)`;;
