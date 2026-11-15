(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_S, catalog title "nat.sym_eq_leb_body_S": for every
  natural number n, Leibniz equality transports every predicate holding of
  the Boolean-valued function that is false at zero and returns leb n q at
  successor input SUC q to leb_body at the successor of n. This file contains
  no proof.
*)

new_constant
  ("logipedia_nat_leb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
   !P:((num -> bool) -> bool).
     P (\m:num.
          if m = 0 then F
          else logipedia_nat_leb n (PRE m))
     ==>
     P (logipedia_nat_leb_body (SUC n))`;;
