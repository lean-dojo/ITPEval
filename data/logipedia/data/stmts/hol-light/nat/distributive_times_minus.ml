(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_minus, catalog title
  "nat.distributive_times_minus": natural-number multiplication distributes
  over truncated natural subtraction on the left. This file contains no proof.
*)

let statement =
  `!a b c:num. a * (b - c) = (a * b) - (a * c)`;;
