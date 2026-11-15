(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_O, catalog title
  "permutation.sym_eq_invert_permut_body_O": Leibniz equality transports every
  predicate holding of the function that returns zero after testing whether
  its input equals the image of zero to the inverse-permutation auxiliary body
  at zero. This file contains no proof.
*)

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `!P:(((num -> num) -> num -> num) -> bool).
     P (\f:num->num. \m:num.
          if m = f 0 then 0 else 0)
     ==>
     P (logipedia_permutation_invert_permut_body 0)`;;
