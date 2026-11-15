(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eqb_true_to_eq, catalog title "nat.eqb_true_to_eq": if the Boolean
  equality test on two natural numbers is true, then the numbers are equal.
  This file contains no proof.
*)

let logipedia_nat_eqb = new_definition
  `logipedia_nat_eqb (n:num) (m:num) <=> n = m`;;

let statement =
  `!n m:num.
     logipedia_nat_eqb n m = T
     ==>
     n = m`;;
