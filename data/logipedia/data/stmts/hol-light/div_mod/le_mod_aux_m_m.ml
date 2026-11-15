(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.le_mod_aux_m_m, catalog title "div_mod.le_mod_aux_m_m": when the
  natural argument is at most the recursion fuel, the fuel-indexed modulus
  auxiliary is at most the natural bound. This file contains no proof.
*)

let logipedia_div_mod_mod_aux = new_recursive_definition num_RECURSION
  `(logipedia_div_mod_mod_aux 0 n m = n) /\
   (logipedia_div_mod_mod_aux (SUC p) n m =
      if n <= m then n
      else logipedia_div_mod_mod_aux p (n - SUC m) m)`;;

let statement =
  `!p n m:num.
     n <= p
     ==>
     logipedia_div_mod_mod_aux p n m <= m`;;
