(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_eqb_false, catalog title "nat.not_eq_to_eqb_false":
  inequality of two natural numbers implies that their Boolean equality test
  is false. This file contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n m:num.
     ~(n = m)
     ==>
     logipedia_nat_eqb n m = F`;;
