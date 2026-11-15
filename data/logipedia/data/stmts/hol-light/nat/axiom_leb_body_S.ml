(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_leb_body_S, catalog title "nat.axiom_leb_body_S": for every
  natural number n, leb_body at the successor of n is equal as a
  Boolean-valued function to the function that is false at zero and returns
  leb n q at each successor q. This file contains no proof.
*)

new_constant
  ("logipedia_nat_leb", `:num -> num -> bool`);;

new_constant
  ("logipedia_nat_leb_body", `:num -> num -> bool`);;

let statement =
  `!n:num.
     (logipedia_nat_leb_body (SUC n)) =
     (\m:num.
        if m = 0 then F
        else logipedia_nat_leb n (PRE m))`;;
