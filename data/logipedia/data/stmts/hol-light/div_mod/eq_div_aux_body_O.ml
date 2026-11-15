(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_div_aux_body_O, catalog title "div_mod.eq_div_aux_body_O":
  Leibniz equality transports every predicate holding of the auxiliary
  division body at natural index zero to the constant-zero binary
  natural-number function. This file contains no proof.
*)

new_constant
  ("logipedia_div_mod_div_aux_body",
   `:num -> num -> num -> num`);;

let statement =
  `!P:((num -> num -> num) -> bool).
     P (logipedia_div_mod_div_aux_body 0) ==>
     P (\m:num. \n:num. 0)`;;
