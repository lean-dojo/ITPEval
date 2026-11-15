(*
  Statement-only formalization of Logipedia corpus artifact nat.associative_times,
  catalog title "nat.associative_times": natural-number multiplication is
  associative, so (x * y) * z equals x * (y * z). This file contains no proof.
*)

let statement =
  `!x y z:num. (x * y) * z = x * (y * z)`;;
