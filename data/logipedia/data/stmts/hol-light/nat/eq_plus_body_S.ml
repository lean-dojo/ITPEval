(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_S, catalog title "nat.eq_plus_body_S": for every natural
  number n, Leibniz equality relates plus_body at the successor of n to the
  function mapping m to the successor of plus n m by predicate transport.
  This file contains no proof.
*)

new_constant
  ("logipedia_nat_plus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_plus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:((num -> num) -> bool).
     P (logipedia_nat_plus_body (SUC n)) ==>
     P (\m:num. SUC (logipedia_nat_plus n m))`;;
