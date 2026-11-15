(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_case,
  catalog title "nat.nat_case": the natural-number case principle, where the
  zero case and all matching successor cases for a predicate imply that the
  predicate holds at the fixed natural number. This file contains no proof.
*)

let statement =
  `!n:num. !P:num->bool.
     (n = 0 ==> P 0) ==>
     (!m:num. n = SUC m ==> P (SUC m)) ==>
     P n`;;
