(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux_body_O, catalog title
  "div_mod.axiom_div_aux_body_O": the source polymorphic equality relation
  identifies the auxiliary division body at natural index zero with the
  constant-zero binary natural-number function. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_div_mod_div_aux_body",
   `:num -> num -> num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_div_mod_div_aux_body 0)
     (\m:num. \n:num. 0)`;;
