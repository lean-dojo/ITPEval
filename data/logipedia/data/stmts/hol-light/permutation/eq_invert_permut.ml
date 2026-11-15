(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.eq_invert_permut, catalog title
  "permutation.eq_invert_permut": for every natural index, Leibniz equality
  transports every predicate holding of the designated inverse-permutation
  function to the natural-type-filtered inverse-permutation body at that
  index. This file contains no proof.
*)

new_constant
  ("logipedia_nat_filter_nat_type", `:(num -> 'a) -> num -> 'a`);;

new_constant
  ("logipedia_permutation_invert_permut",
   `:num -> (num -> num) -> num -> num`);;

new_constant
  ("logipedia_permutation_invert_permut_body",
   `:num -> (num -> num) -> num -> num`);;

let statement =
  `!n:num.
   !P:(((num -> num) -> num -> num) -> bool).
     P (logipedia_permutation_invert_permut n)
     ==>
     P (logipedia_nat_filter_nat_type
          logipedia_permutation_invert_permut_body n)`;;
