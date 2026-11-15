(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_body_S, catalog title "nat.eq_minus_body_S": Leibniz equality
  relates the subtraction body at a successor to its natural-number case
  function on the second argument. This file contains no proof.
*)

new_constant
  ("logipedia_nat_minus", `:num -> num -> num`);;

new_constant
  ("logipedia_nat_minus_body", `:num -> num -> num`);;

let statement =
  `!n:num.
   !P:(num->num)->bool.
     P (logipedia_nat_minus_body (SUC n))
     ==>
     P (\m:num.
          if m = 0 then SUC n
          else logipedia_nat_minus n (PRE m))`;;
