(*
  Statement-only formalization of Logipedia corpus artifact nat.associative_plus,
  catalog title "nat.associative_plus": natural-number addition is associative,
  so (x + y) + z equals x + (y + z). This file contains no proof.
*)

let statement =
  `!x y z:num. (x + y) + z = x + (y + z)`;;
