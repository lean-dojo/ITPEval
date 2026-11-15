(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_div_aux, catalog title "div_mod.eq_div_aux": for every natural
  index p, Leibniz equality transports every predicate holding of the
  designated division auxiliary function at p to the filtered auxiliary body
  at p. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_div_mod_div_aux", `:num -> num -> num -> num`);;

new_constant
  ("logipedia_div_mod_div_aux_body", `:num -> num -> num -> num`);;

let statement =
  `!p:num.
   !P:((num -> num -> num) -> bool).
     P (logipedia_div_mod_div_aux p)
     ==>
     P (logipedia_nat_filter_nat_type
          logipedia_div_mod_div_aux_body p)`;;
