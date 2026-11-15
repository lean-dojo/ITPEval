(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_O, catalog title "nat.eq_plus_body_O": Leibniz equality
  relates plus_body at natural zero to the identity function on natural
  numbers by predicate transport. This file contains no proof.
*)

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!P:((num -> num) -> bool).
     P (logipedia_nat_plus_body 0) ==>
     P (\m:num. m)`;;
