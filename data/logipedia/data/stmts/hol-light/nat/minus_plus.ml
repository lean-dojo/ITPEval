(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_plus,
  catalog title "nat.minus_plus": for all natural numbers n, m, and p,
  subtracting m and then p from n equals subtracting m + p from n, using
  truncated natural subtraction. This file contains no proof.
*)

let statement =
  `!n m p:num. (n - m) - p = n - (m + p)`;;
