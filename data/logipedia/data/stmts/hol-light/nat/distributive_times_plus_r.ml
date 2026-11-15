(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus_r, catalog title
  "nat.distributive_times_plus_r": natural-number multiplication distributes
  over addition on the right. This file contains no proof.
*)

let statement =
  `!a b c:num. (b + c) * a = (b * a) + (c * a)`;;
