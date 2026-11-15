(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injective_transpose, catalog title
  "permutation.injective_transpose": every transposition of two natural
  numbers is an injective function on the natural numbers. This file contains
  no proof.
*)

let logipedia_permutation_transpose = new_definition
  `logipedia_permutation_transpose (i:num) (j:num) (n:num) =
     if n = i then j else if n = j then i else n`;;

let statement =
  `!i j x y:num.
     logipedia_permutation_transpose i j x =
     logipedia_permutation_transpose i j y
     ==> x = y`;;
