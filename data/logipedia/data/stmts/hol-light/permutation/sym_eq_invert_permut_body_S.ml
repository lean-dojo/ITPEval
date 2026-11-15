(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_S, catalog title
  "permutation.sym_eq_invert_permut_body_S": at every successor natural
  index, Leibniz equality transports every predicate holding of the function
  that returns that successor when its input equals the function's value
  there, and otherwise uses the preceding inverse-permutation function, to
  the inverse-permutation auxiliary body. This file contains no proof.
*)

new_constant
  ("logipedia_permutation_invert_permut",
   `:num -> (num -> num) -> num -> num`);;

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `!n:num.
   !P:(((num -> num) -> num -> num) -> bool).
     P (\f:num->num. \m:num.
          if m = f (SUC n) then SUC n
          else logipedia_permutation_invert_permut n f m)
     ==>
     P (logipedia_permutation_invert_permut_body (SUC n))`;;
