(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus, catalog title
  "nat.distributive_times_plus": natural-number multiplication distributes
  over addition on the left. This file contains no proof.
*)

let statement =
  `!a b c:num. a * (b + c) = (a * b) + (a * c)`;;
