(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_minus_body_S, catalog title "nat.axiom_minus_body_S": the
  successor case equation for the natural-number subtraction body, expressed
  using case analysis on its second argument. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_nat_minus_body (SUC n))
       (\m:num.
          if m = 0 then SUC n
          else logipedia_nat_minus n (PRE m))`;;
