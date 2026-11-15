(*
  Statement-only formalization of Logipedia corpus artifact
  nat.axiom_eqb_body_O, catalog title "nat.axiom_eqb_body_O": eqb_body at
  zero is equal as a Boolean-valued function to the function that is true at
  zero and false at every successor. This file contains no proof.
*)

new_constant
  ("logipedia_nat_eqb_body", `:num -> num -> bool`);;

let statement =
  `(logipedia_nat_eqb_body 0) =
   (\m:num. if m = 0 then T else F)`;;
