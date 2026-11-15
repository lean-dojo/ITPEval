(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_eqb_body_S, catalog title "nat.eq_eqb_body_S": for every natural
  number n, Leibniz equality transports every predicate holding of eqb_body
  at the successor of n to the Boolean-valued function that is false at zero
  and returns eqb n q at each successor q. This file contains no proof.
*)

new_constant
  ("logipedia_nat_eqb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_eqb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
   !P:((num -> bool) -> bool).
     P (logipedia_nat_eqb_body (SUC n)) ==>
     P (\m:num.
          if m = 0 then F
          else logipedia_nat_eqb n (PRE m))`;;
