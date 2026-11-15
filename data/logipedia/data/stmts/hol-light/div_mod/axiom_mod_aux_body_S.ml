(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_S, catalog title
  "div_mod.axiom_mod_aux_body_S": for every natural index p, the source
  polymorphic equality relation identifies the successor-indexed auxiliary
  modulus body with the binary natural-number function that returns m when m
  is at most n and otherwise returns the recursive auxiliary value at p, m
  minus successor n, and n. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_div_mod_mod_aux",
   `:num -> num -> num -> num`);;

new_constant
  ("logipedia_div_mod_mod_aux_body",
   `:num -> num -> num -> num`);;

let statement =
  `!p:num.
     logipedia_connectives_equal
       (logipedia_div_mod_mod_aux_body (SUC p))
       (\m:num. \n:num.
          if m <= n then m
          else logipedia_div_mod_mod_aux p (m - SUC n) n)`;;
