(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut_body_O, catalog title
  "permutation.axiom_invert_permut_body_O": the source polymorphic equality
  relation identifies the inverse-permutation auxiliary body at natural index
  zero with the function that returns zero after testing whether its input
  equals the image of zero. This file contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `logipedia_connectives_equal
     (logipedia_permutation_invert_permut_body 0)
     (\f:num->num. \m:num.
        if m = f 0 then 0 else 0)`;;
