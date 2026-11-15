(* Statement-only formalization of Logipedia artifact
   permutation.bijn_transpose (catalog title: permutation.bijn_transpose):
   bounded surjectivity of a natural-number transposition on an initial
   segment. This file contains no proof. *)

let permutation_transpose = new_definition
  `permutation_transpose (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let permutation_bijn = new_definition
  `permutation_bijn (f:num->num) n <=>
     !m. m <= n ==> ?p. p <= n /\ f p = m`;;

let BIJN_TRANSPOSE =
  `!n i j:num.
     i <= n ==> j <= n ==>
     permutation_bijn (permutation_transpose i j) n`;;
