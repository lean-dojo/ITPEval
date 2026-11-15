(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_S, catalog title
  "permutation.axiom_invert_permut_body_S": at every successor natural index,
  the source polymorphic equality relation identifies the inverse-permutation
  auxiliary body with the function that returns that successor when its input
  equals the function's value there, and otherwise uses the preceding
  inverse-permutation function. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_permutation_invert_permut",
   `:num -> (num -> num) -> num -> num`);;

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `!n:num.
     logipedia_connectives_equal
       (logipedia_permutation_invert_permut_body (SUC n))
       (\f:num->num. \m:num.
          if m = f (SUC n) then SUC n
          else logipedia_permutation_invert_permut n f m)`;;
