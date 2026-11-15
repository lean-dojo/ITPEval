(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_false_to_not_eq, catalog title "nat.eqb_false_to_not_eq": if the
  Boolean equality test on two natural numbers is false, then the numbers are
  unequal. This file contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n m:num.
     logipedia_nat_eqb n m = F
     ==>
     ~(n = m)`;;
