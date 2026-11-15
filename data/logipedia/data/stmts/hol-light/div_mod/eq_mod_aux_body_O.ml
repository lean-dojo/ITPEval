(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_mod_aux_body_O, catalog title "div_mod.eq_mod_aux_body_O":
  Leibniz equality transports every predicate holding of the auxiliary
  modulus body at natural index zero to the binary natural-number function
  that returns its first argument. This file contains no proof.
*)

new_constant
  ("logipedia_div_mod_mod_aux_body",
   `:num -> num -> num -> num`);;

let statement =
  `!P:((num -> num -> num) -> bool).
     P (logipedia_div_mod_mod_aux_body 0) ==>
     P (\m:num. \n:num. m)`;;
