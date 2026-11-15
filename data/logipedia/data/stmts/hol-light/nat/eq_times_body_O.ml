(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_O, catalog title "nat.eq_times_body_O": Leibniz equality
  transports every predicate holding of times_body at natural zero to the
  constant-zero function on natural numbers. This file contains no proof.
*)

new_constant
  ("logipedia_nat_times_body", `:num -> num -> num`);;

let statement =
  `!P:((num -> num) -> bool).
     P (logipedia_nat_times_body 0) ==>
     P (\m:num. 0)`;;
