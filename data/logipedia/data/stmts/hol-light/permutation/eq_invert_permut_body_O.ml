(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut_body_O, catalog title
  "permutation.eq_invert_permut_body_O": Leibniz equality transports every
  predicate holding of the inverse-permutation auxiliary body at zero to the
  function that returns zero after testing whether its input equals the image
  of zero. This file contains no proof.
*)

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `!P:(((num -> num) -> num -> num) -> bool).
     P (logipedia_permutation_invert_permut_body 0)
     ==>
     P (\f:num->num. \m:num.
          if m = f 0 then 0 else 0)`;;
