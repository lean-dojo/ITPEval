(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_eqb_body_O, catalog title "nat.sym_eq_eqb_body_O": Leibniz
  equality transports every predicate holding of the Boolean-valued function
  that is true at zero and false at every successor to eqb_body at zero.
  This file contains no proof.
*)

new_constant
  ("logipedia_nat_eqb_body", `:num -> num -> bool`);;

let statement =
  `!P:((num -> bool) -> bool).
     P (\m:num. if m = 0 then T else F) ==>
     P (logipedia_nat_eqb_body 0)`;;
