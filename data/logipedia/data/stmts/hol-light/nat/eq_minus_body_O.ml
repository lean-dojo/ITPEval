(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_body_O, catalog title "nat.eq_minus_body_O": Leibniz equality
  relates minus_body at natural zero to the constant-zero function on natural
  numbers by predicate transport. This file contains no proof.
*)

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!P:((num -> num) -> bool).
     P (logipedia_nat_minus_body 0) ==>
     P (\m:num. 0)`;;
