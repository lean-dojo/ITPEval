(*
  Statement-only formalization of Logipedia corpus artifact
  nat.injective_plus_r, catalog title "nat.injective_plus_r": for every
  natural number n, the map sending m to n + m is injective. This file
  contains no proof.
*)

let statement =
  `!n m1 m2:num. n + m1 = n + m2 ==> m1 = m2`;;
