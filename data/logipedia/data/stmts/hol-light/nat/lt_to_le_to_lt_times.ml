(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_le_to_lt_times, catalog title "nat.lt_to_le_to_lt_times":
  natural-number multiplication preserves a strict inequality when the first
  factors are strictly ordered, the second factors are weakly ordered, and
  the upper second factor is positive. This file contains no proof.
*)

let statement =
  `!n m p q:num.
     n < m
     ==> p <= q
     ==> 0 < q
     ==> n * p < m * q`;;
