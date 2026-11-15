(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.axiom_invert_permut, catalog title
  "permutation.axiom_invert_permut": for every natural index, the designated
  inverse-permutation function is related by the source polymorphic equality
  relation to the filtered inverse-permutation body at that index. This file
  contains no proof.
*)

new_constant
  ("logipedia_connectives_equal", `:'a -> 'a -> bool`);;

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
     logipedia_connectives_equal
       (logipedia_permutation_invert_permut n)
       (logipedia_nat_filter_nat_type
          logipedia_permutation_invert_permut_body n)`;;
