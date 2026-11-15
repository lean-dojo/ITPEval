(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_div_aux, catalog title "div_mod.axiom_div_aux": for every
  natural index p, the designated division auxiliary function at p is related
  by the source polymorphic equality relation to the filtered auxiliary body
  at p. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_div_mod_div_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_div_mod_div_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
     logipedia_connectives_equal
       (logipedia_div_mod_div_aux p)
       (logipedia_nat_filter_nat_type
          logipedia_div_mod_div_aux_body p)`;;
