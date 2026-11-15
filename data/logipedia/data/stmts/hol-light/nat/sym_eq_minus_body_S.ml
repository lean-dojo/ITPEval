(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_minus_body_S, catalog title "nat.sym_eq_minus_body_S": Leibniz
  equality transports every predicate holding of the natural-number case
  function for subtraction at a successor to minus_body at that successor.
  This file contains no proof.
*)

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:(num->num)->bool.
     P (\m:num.
          if m = 0 then SUC n
          else logipedia_nat_minus n (PRE m))
     ==>
     P (logipedia_nat_minus_body (SUC n))`;;
