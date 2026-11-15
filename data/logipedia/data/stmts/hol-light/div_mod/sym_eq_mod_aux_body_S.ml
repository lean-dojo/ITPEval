(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_mod_aux_body_S, catalog title
  "div_mod.sym_eq_mod_aux_body_S": for every natural index p, Leibniz equality
  transports every predicate holding of the binary natural-number function
  that returns m when m is at most n and otherwise returns the recursive
  auxiliary modulus value at p, m minus successor n, and n, to the
  successor-indexed auxiliary modulus body. This file contains no proof.
*)

new_constant
  ("logipedia_div_mod_mod_aux",
   `:num -> num -> num -> num`);;

new_constant
  ("logipedia_div_mod_mod_aux_body",
   `:num -> num -> num -> num`);;

let statement =
  `!p:num.
   !P:((num -> num -> num) -> bool).
     P (\m:num. \n:num.
          if m <= n then m
          else logipedia_div_mod_mod_aux p (m - SUC n) n)
     ==>
     P (logipedia_div_mod_mod_aux_body (SUC p))`;;
