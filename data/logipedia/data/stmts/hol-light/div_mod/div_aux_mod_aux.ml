(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_aux_mod_aux, catalog title "div_mod.div_aux_mod_aux": the
  fuel-indexed auxiliary quotient and remainder functions decompose every
  natural number as quotient times successor modulus plus remainder. This
  file contains no proof.
*)

let logipedia_div_mod_mod_aux = new_recursive_definition num_RECURSION
  `(logipedia_div_mod_mod_aux 0 n m = n) /\
   (logipedia_div_mod_mod_aux (SUC p) n m =
      if n <= m then n
      else logipedia_div_mod_mod_aux p (n - SUC m) m)`;;

let logipedia_div_mod_div_aux = new_recursive_definition num_RECURSION
  `(logipedia_div_mod_div_aux 0 n m = 0) /\
   (logipedia_div_mod_div_aux (SUC p) n m =
      if n <= m then 0
      else SUC (logipedia_div_mod_div_aux p (n - SUC m) m))`;;

let statement =
  `!p n m:num.
     n =
     logipedia_div_mod_div_aux p n m * SUC m +
     logipedia_div_mod_mod_aux p n m`;;
