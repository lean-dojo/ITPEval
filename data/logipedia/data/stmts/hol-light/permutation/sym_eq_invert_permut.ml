(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.sym_eq_invert_permut, catalog title
  "permutation.sym_eq_invert_permut": for every natural index, Leibniz
  equality transports every predicate holding of the natural-type-filtered
  inverse-permutation body to the designated inverse-permutation function at
  that index. This file contains no proof.
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
     P (logipedia_nat_filter_nat_type
          logipedia_permutation_invert_permut_body n)
     ==>
     P (logipedia_permutation_invert_permut n)`;;
