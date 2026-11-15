(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_to_eqb_true, catalog title "nat.eq_to_eqb_true": equality of two
  natural numbers implies that their Boolean equality test is true. This file
  contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n m:num.
     n = m
     ==>
     logipedia_nat_eqb n m = T`;;
